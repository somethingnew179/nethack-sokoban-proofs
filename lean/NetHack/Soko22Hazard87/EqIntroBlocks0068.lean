import NetHack.Soko22Hazard87.EqIntroBlocks0067
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro17000 (p : Pattern) (selected : d185710 p = 0) : d187004 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185654 q = 0) : d186975 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185654, d186975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16986 q selected
    | true =>
      simp only [d185654, d186975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185655 q = 0) : d186976 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185655, d186976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185655, d186976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185593 q = 0) : d186914 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185593, d186914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16972 q selected
    | true =>
      simp only [d185593, d186914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185594 q = 0) : d186915 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185594, d186915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185594, d186915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185656 q = 0) : d186977 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185656, d186977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185656, d186977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185657 q = 0) : d186978 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185657, d186978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185657, d186978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185658 q = 0) : d186979 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185658, d186979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185658, d186979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185710 q = 0) : d187004 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185710, d187004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185710, d187004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17001 (p : Pattern) (selected : d185712 p = 0) : d186936 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185673 q = 0) : d186914 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185673, d186914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16990 q selected
    | true =>
      simp only [d185673, d186914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185674 q = 0) : d186915 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185674, d186915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185674, d186915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185677 q = 0) : d186918 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185677, d186918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16991 q selected
    | true =>
      simp only [d185677, d186918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185678 q = 0) : d186919 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185678, d186919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185678, d186919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185679 q = 0) : d186920 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185679, d186920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185679, d186920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185680 q = 0) : d186921 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185680, d186921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185680, d186921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185681 q = 0) : d186922 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185681, d186922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185681, d186922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185712 q = 0) : d186936 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185712, d186936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185712, d186936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17002 (p : Pattern) (selected : d185713 p = 0) : d186937 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185677 q = 0) : d186918 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185677, d186918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16991 q selected
    | true =>
      simp only [d185677, d186918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185678 q = 0) : d186919 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185678, d186919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185678, d186919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185683 q = 0) : d186924 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185683, d186924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185683, d186924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185684 q = 0) : d186925 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185684, d186925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185684, d186925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185685 q = 0) : d186926 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185685, d186926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185685, d186926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185713 q = 0) : d186937 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185713, d186937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185713, d186937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17003 (p : Pattern) (selected : d185716 p = 0) : d187007 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185593 q = 0) : d186914 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185593, d186914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16972 q selected
    | true =>
      simp only [d185593, d186914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185594 q = 0) : d186915 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185594, d186915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185594, d186915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185689 q = 0) : d186983 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185689, d186983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185689, d186983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185690 q = 0) : d186984 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185690, d186984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185690, d186984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185691 q = 0) : d186985 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185691, d186985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185691, d186985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185716 q = 0) : d187007 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185716, d187007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185716, d187007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17004 (p : Pattern) (selected : d185722 p = 0) : d187013 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185630 q = 0) : d186951 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185630, d186951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16980 q selected
    | true =>
      simp only [d185630, d186951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16981 q selected
  have h2 (q : Pattern) (selected : d185631 q = 0) : d186952 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185631, d186952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185631, d186952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185632 q = 0) : d186953 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185632, d186953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185632, d186953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185633 q = 0) : d186954 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185633, d186954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185633, d186954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185640 q = 0) : d186961 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185640, d186961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16982 q selected
    | true =>
      simp only [d185640, d186961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16983 q selected
  have h6 (q : Pattern) (selected : d185641 q = 0) : d186962 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185641, d186962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185641, d186962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185642 q = 0) : d186963 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185642, d186963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185642, d186963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185660 q = 0) : d186981 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185660, d186981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16987 q selected
    | true =>
      simp only [d185660, d186981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16974 q selected
  have h9 (q : Pattern) (selected : d185687 q = 0) : d186928 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185687, d186928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16992 q selected
    | true =>
      simp only [d185687, d186928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16993 q selected
  have h10 (q : Pattern) (selected : d185688 q = 0) : d186982 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185688, d186982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d185688, d186982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185693 q = 0) : d186987 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185693, d186987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16994 q selected
    | true =>
      simp only [d185693, d186987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d185694 q = 0) : d186988 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185694, d186988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d185694, d186988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d185695 q = 0) : d186989 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185695, d186989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d185695, d186989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d185696 q = 0) : d186990 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185696, d186990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185696, d186990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d185697 q = 0) : d186991 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185697, d186991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185697, d186991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d185701 q = 0) : d186995 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185701, d186995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16996 q selected
    | true =>
      simp only [d185701, d186995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16997 q selected
  have h17 (q : Pattern) (selected : d185702 q = 0) : d186996 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185702, d186996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185702, d186996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d185703 q = 0) : d186997 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185703, d186997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d185703, d186997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d185704 q = 0) : d186998 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185704, d186998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185704, d186998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d185707 q = 0) : d187001 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185707, d187001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16998 q selected
    | true =>
      simp only [d185707, d187001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16999 q selected
  have h21 (q : Pattern) (selected : d185708 q = 0) : d187002 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185708, d187002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185708, d187002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d185709 q = 0) : d187003 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185709, d187003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d185709, d187003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d185711 q = 0) : d187005 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185711, d187005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17000 q selected
    | true =>
      simp only [d185711, d187005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16977 q selected
  have h24 (q : Pattern) (selected : d185714 q = 0) : d186938 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185714, d186938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17001 q selected
    | true =>
      simp only [d185714, d186938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17002 q selected
  have h25 (q : Pattern) (selected : d185715 q = 0) : d187006 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185715, d187006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d185715, d187006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d185717 q = 0) : d187008 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185717, d187008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17003 q selected
    | true =>
      simp only [d185717, d187008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d185718 q = 0) : d187009 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185718, d187009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d185718, d187009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d185719 q = 0) : d187010 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185719, d187010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d185719, d187010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d185720 q = 0) : d187011 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185720, d187011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d185720, d187011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d185721 q = 0) : d187012 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185721, d187012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d185721, d187012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d185722 q = 0) : d187013 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185722, d187013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d185722, d187013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro17005 (p : Pattern) (selected : d185729 p = 0) : d187020 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185607 q = 0) : d186928 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185607, d186928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16974 q selected
    | true =>
      simp only [d185607, d186928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16975 q selected
  have h2 (q : Pattern) (selected : d185608 q = 0) : d186929 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185608, d186929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185608, d186929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185609 q = 0) : d186930 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185609, d186930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185609, d186930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185610 q = 0) : d186931 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185610, d186931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185610, d186931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185611 q = 0) : d186932 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185611, d186932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185611, d186932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185724 q = 0) : d187015 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185724, d187015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16975 q selected
    | true =>
      simp only [d185724, d187015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185725 q = 0) : d187016 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185725, d187016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185725, d187016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185726 q = 0) : d187017 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185726, d187017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185726, d187017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d185727 q = 0) : d187018 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185727, d187018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185727, d187018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185728 q = 0) : d187019 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185728, d187019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185728, d187019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185729 q = 0) : d187020 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185729, d187020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185729, d187020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro17006 (p : Pattern) (selected : d185735 p = 0) : d187026 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185724 q = 0) : d187015 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185724, d187015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16975 q selected
    | true =>
      simp only [d185724, d187015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185725 q = 0) : d187016 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185725, d187016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185725, d187016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185726 q = 0) : d187017 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185726, d187017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185726, d187017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185727 q = 0) : d187018 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185727, d187018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185727, d187018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185728 q = 0) : d187019 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185728, d187019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185728, d187019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185730 q = 0) : d187021 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185730, d187021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16978 q selected
    | true =>
      simp only [d185730, d187021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185731 q = 0) : d187022 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185731, d187022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185731, d187022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185732 q = 0) : d187023 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185732, d187023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185732, d187023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d185733 q = 0) : d187024 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185733, d187024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185733, d187024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185734 q = 0) : d187025 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185734, d187025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185734, d187025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185735 q = 0) : d187026 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185735, d187026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185735, d187026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro17007 (p : Pattern) (selected : d185742 p = 0) : d187033 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185711 q = 0) : d187005 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185711, d187005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17000 q selected
    | true =>
      simp only [d185711, d187005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16977 q selected
  have h2 (q : Pattern) (selected : d185714 q = 0) : d186938 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185714, d186938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17001 q selected
    | true =>
      simp only [d185714, d186938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17002 q selected
  have h3 (q : Pattern) (selected : d185715 q = 0) : d187006 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185715, d187006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185715, d187006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185717 q = 0) : d187008 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185717, d187008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17003 q selected
    | true =>
      simp only [d185717, d187008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185718 q = 0) : d187009 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185718, d187009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185718, d187009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185719 q = 0) : d187010 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185719, d187010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185719, d187010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185740 q = 0) : d187031 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185740, d187031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185740, d187031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185741 q = 0) : d187032 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185741, d187032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185741, d187032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d185742 q = 0) : d187033 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185742, d187033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185742, d187033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro17008 (p : Pattern) (selected : d185744 p = 0) : d187035 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185730 q = 0) : d187021 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185730, d187021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16978 q selected
    | true =>
      simp only [d185730, d187021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185731 q = 0) : d187022 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185731, d187022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185731, d187022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185732 q = 0) : d187023 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185732, d187023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185732, d187023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185733 q = 0) : d187024 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185733, d187024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185733, d187024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185734 q = 0) : d187025 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185734, d187025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185734, d187025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185744 q = 0) : d187035 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185744, d187035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185744, d187035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17009 (p : Pattern) (selected : d185750 p = 0) : d187041 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d17004 q = 0) : d127738 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17004, d127738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17004, d127738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6711 q selected
  have h2 (q : Pattern) (selected : d10036 q = 0) : d101463 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10036, d101463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6711 q selected
    | true =>
      simp only [d10036, d101463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d17005 q = 0) : d127739 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17005, d127739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d17005, d127739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10038 q = 0) : d101465 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10038, d101465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10038, d101465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17006 q = 0) : d127740 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17006, d127740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17006, d127740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15387 q = 0) : d123426 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15387, d123426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15387, d123426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6714 q selected
  have h7 (q : Pattern) (selected : d10063 q = 0) : d101490 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10063, d101490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6714 q selected
    | true =>
      simp only [d10063, d101490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15388 q = 0) : d123427 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15388, d123427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15388, d123427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10065 q = 0) : d101492 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10065, d101492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10065, d101492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15389 q = 0) : d123428 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15389, d123428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15389, d123428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185750 q = 0) : d187041 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185750, d187041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185750, d187041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro17010 (p : Pattern) (selected : d185751 p = 0) : d187042 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d17011 q = 0) : d127745 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17011, d127745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17011, d127745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6716 q selected
  have h2 (q : Pattern) (selected : d10074 q = 0) : d101501 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10074, d101501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6716 q selected
    | true =>
      simp only [d10074, d101501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d17012 q = 0) : d127746 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17012, d127746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d17012, d127746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10076 q = 0) : d101503 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10076, d101503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10076, d101503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17013 q = 0) : d127747 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17013, d127747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17013, d127747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15397 q = 0) : d123436 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15397, d123436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15397, d123436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6717 q selected
  have h7 (q : Pattern) (selected : d10085 q = 0) : d101512 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6717 q selected
    | true =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15398 q = 0) : d123437 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15398, d123437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15398, d123437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10087 q = 0) : d101514 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15399 q = 0) : d123438 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15399, d123438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15399, d123438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185751 q = 0) : d187042 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185751, d187042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185751, d187042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro17011 (p : Pattern) (selected : d185755 p = 0) : d187046 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d15397 q = 0) : d123436 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15397, d123436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15397, d123436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6717 q selected
  have h2 (q : Pattern) (selected : d10085 q = 0) : d101512 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6717 q selected
    | true =>
      simp only [d10085, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15398 q = 0) : d123437 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15398, d123437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15398, d123437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10087 q = 0) : d101514 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10087, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15399 q = 0) : d123438 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15399, d123438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15399, d123438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185755 q = 0) : d187046 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185755, d187046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185755, d187046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17012 (p : Pattern) (selected : d185760 p = 0) : d187051 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d17027 q = 0) : d127761 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17027, d127761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17027, d127761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6721 q selected
  have h2 (q : Pattern) (selected : d10115 q = 0) : d101542 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10115, d101542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6721 q selected
    | true =>
      simp only [d10115, d101542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d17028 q = 0) : d127762 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17028, d127762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d17028, d127762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10117 q = 0) : d101544 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10117, d101544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10117, d101544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17029 q = 0) : d127763 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17029, d127763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17029, d127763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185760 q = 0) : d187051 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185760, d187051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185760, d187051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17013 (p : Pattern) (selected : d185769 p = 0) : d187060 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185752 q = 0) : d187043 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185752, d187043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17009 q selected
    | true =>
      simp only [d185752, d187043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17010 q selected
  have h2 (q : Pattern) (selected : d185753 q = 0) : d187044 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185753, d187044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185753, d187044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185754 q = 0) : d187045 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185754, d187045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185754, d187045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185756 q = 0) : d187047 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185756, d187047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17010 q selected
    | true =>
      simp only [d185756, d187047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17011 q selected
  have h5 (q : Pattern) (selected : d185757 q = 0) : d187048 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185757, d187048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185757, d187048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185758 q = 0) : d187049 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185758, d187049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185758, d187049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185759 q = 0) : d187050 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185759, d187050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185759, d187050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185761 q = 0) : d187052 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185761, d187052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17010 q selected
    | true =>
      simp only [d185761, d187052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17012 q selected
  have h9 (q : Pattern) (selected : d185762 q = 0) : d187053 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185762, d187053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185762, d187053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185763 q = 0) : d187054 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185763, d187054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185763, d187054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185764 q = 0) : d187055 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185764, d187055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17012 q selected
    | true =>
      simp only [d185764, d187055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d185765 q = 0) : d187056 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185765, d187056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185765, d187056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d185766 q = 0) : d187057 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185766, d187057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185766, d187057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d185767 q = 0) : d187058 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185767, d187058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d185767, d187058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d185768 q = 0) : d187059 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185768, d187059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185768, d187059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d185769 q = 0) : d187060 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185769, d187060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d185769, d187060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro17014 (p : Pattern) (selected : d185774 p = 0) : d187065 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185761 q = 0) : d187052 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185761, d187052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17010 q selected
    | true =>
      simp only [d185761, d187052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17012 q selected
  have h2 (q : Pattern) (selected : d185762 q = 0) : d187053 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185762, d187053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185762, d187053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185763 q = 0) : d187054 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185763, d187054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185763, d187054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185764 q = 0) : d187055 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185764, d187055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17012 q selected
    | true =>
      simp only [d185764, d187055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185765 q = 0) : d187056 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185765, d187056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185765, d187056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185766 q = 0) : d187057 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185766, d187057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185766, d187057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185767 q = 0) : d187058 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185767, d187058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185767, d187058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185772 q = 0) : d187063 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185772, d187063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185772, d187063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d185773 q = 0) : d187064 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185773, d187064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185773, d187064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185774 q = 0) : d187065 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185774, d187065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d185774, d187065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro17015 (p : Pattern) (selected : d185780 p = 0) : d187071 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185770 q = 0) : d187061 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185770, d187061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17013 q selected
    | true =>
      simp only [d185770, d187061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185771 q = 0) : d187062 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185771, d187062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185771, d187062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185775 q = 0) : d187066 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185775, d187066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17014 q selected
    | true =>
      simp only [d185775, d187066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185776 q = 0) : d187067 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185776, d187067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185776, d187067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185777 q = 0) : d187068 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185777, d187068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185777, d187068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185778 q = 0) : d187069 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185778, d187069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185778, d187069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185779 q = 0) : d187070 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185779, d187070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185779, d187070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185780 q = 0) : d187071 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185780, d187071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185780, d187071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17016 (p : Pattern) (selected : d185782 p = 0) : d187073 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185764 q = 0) : d187055 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185764, d187055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17012 q selected
    | true =>
      simp only [d185764, d187055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185765 q = 0) : d187056 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185765, d187056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185765, d187056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185766 q = 0) : d187057 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185766, d187057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185766, d187057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185772 q = 0) : d187063 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185772, d187063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185772, d187063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185781 q = 0) : d187072 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185781, d187072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185781, d187072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185782 q = 0) : d187073 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185782, d187073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185782, d187073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17017 (p : Pattern) (selected : d185788 p = 0) : d187079 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185775 q = 0) : d187066 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185775, d187066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17014 q selected
    | true =>
      simp only [d185775, d187066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185776 q = 0) : d187067 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185776, d187067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185776, d187067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185783 q = 0) : d187074 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185783, d187074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17016 q selected
    | true =>
      simp only [d185783, d187074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185784 q = 0) : d187075 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185784, d187075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185784, d187075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185785 q = 0) : d187076 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185785, d187076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185785, d187076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185786 q = 0) : d187077 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185786, d187077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185786, d187077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185787 q = 0) : d187078 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185787, d187078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185787, d187078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185788 q = 0) : d187079 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185788, d187079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185788, d187079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17018 (p : Pattern) (selected : d185790 p = 0) : d187042 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d17066 q = 0) : d127745 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17066, d127745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17066, d127745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6733 q selected
  have h2 (q : Pattern) (selected : d10190 q = 0) : d101501 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10190, d101501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6733 q selected
    | true =>
      simp only [d10190, d101501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d17067 q = 0) : d127746 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17067, d127746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d17067, d127746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10192 q = 0) : d101503 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10192, d101503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10192, d101503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17068 q = 0) : d127747 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17068, d127747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17068, d127747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15457 q = 0) : d123436 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15457, d123436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15457, d123436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6735 q selected
  have h7 (q : Pattern) (selected : d10215 q = 0) : d101512 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10215, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6735 q selected
    | true =>
      simp only [d10215, d101512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15458 q = 0) : d123437 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15458, d123437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15458, d123437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10217 q = 0) : d101514 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10217, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10217, d101514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15459 q = 0) : d123438 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15459, d123438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15459, d123438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185790 q = 0) : d187042 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185790, d187042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185790, d187042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro17019 (p : Pattern) (selected : d185791 p = 0) : d187051 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d17073 q = 0) : d127761 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17073, d127761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17073, d127761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6737 q selected
  have h2 (q : Pattern) (selected : d10226 q = 0) : d101542 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10226, d101542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6737 q selected
    | true =>
      simp only [d10226, d101542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d17074 q = 0) : d127762 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17074, d127762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d17074, d127762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10228 q = 0) : d101544 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10228, d101544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10228, d101544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17075 q = 0) : d127763 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17075, d127763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17075, d127763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185791 q = 0) : d187051 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185791, d187051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185791, d187051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17020 (p : Pattern) (selected : d185801 p = 0) : d187065 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185792 q = 0) : d187052 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185792, d187052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17018 q selected
    | true =>
      simp only [d185792, d187052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17019 q selected
  have h2 (q : Pattern) (selected : d185793 q = 0) : d187053 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185793, d187053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185793, d187053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185794 q = 0) : d187054 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185794, d187054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185794, d187054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185795 q = 0) : d187055 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185795, d187055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17019 q selected
    | true =>
      simp only [d185795, d187055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185796 q = 0) : d187056 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185796, d187056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185796, d187056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185797 q = 0) : d187057 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185797, d187057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185797, d187057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185798 q = 0) : d187058 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185798, d187058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185798, d187058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185799 q = 0) : d187063 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185799, d187063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185799, d187063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d185800 q = 0) : d187064 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185800, d187064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185800, d187064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185801 q = 0) : d187065 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185801, d187065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d185801, d187065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro17021 (p : Pattern) (selected : d185805 p = 0) : d187073 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185795 q = 0) : d187055 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185795, d187055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17019 q selected
    | true =>
      simp only [d185795, d187055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185796 q = 0) : d187056 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185796, d187056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185796, d187056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185797 q = 0) : d187057 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185797, d187057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185797, d187057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185799 q = 0) : d187063 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185799, d187063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185799, d187063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185804 q = 0) : d187072 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185804, d187072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185804, d187072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185805 q = 0) : d187073 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185805, d187073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185805, d187073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17022 (p : Pattern) (selected : d185811 p = 0) : d187079 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185802 q = 0) : d187066 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185802, d187066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17020 q selected
    | true =>
      simp only [d185802, d187066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185803 q = 0) : d187067 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185803, d187067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185803, d187067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185806 q = 0) : d187074 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185806, d187074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17021 q selected
    | true =>
      simp only [d185806, d187074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185807 q = 0) : d187075 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185807, d187075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185807, d187075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185808 q = 0) : d187076 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185808, d187076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185808, d187076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185809 q = 0) : d187077 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185809, d187077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185809, d187077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185810 q = 0) : d187078 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185810, d187078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185810, d187078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185811 q = 0) : d187079 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185811, d187079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185811, d187079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17023 (p : Pattern) (selected : d185815 p = 0) : d187084 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185806 q = 0) : d187074 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185806, d187074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17021 q selected
    | true =>
      simp only [d185806, d187074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185807 q = 0) : d187075 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185807, d187075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185807, d187075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185812 q = 0) : d187081 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185812, d187081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185812, d187081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185813 q = 0) : d187082 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185813, d187082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185813, d187082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185814 q = 0) : d187083 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185814, d187083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185814, d187083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185815 q = 0) : d187084 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185815, d187084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185815, d187084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17024 (p : Pattern) (selected : d185821 p = 0) : d187090 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185775 q = 0) : d187066 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185775, d187066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17014 q selected
    | true =>
      simp only [d185775, d187066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185776 q = 0) : d187067 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185776, d187067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185776, d187067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185818 q = 0) : d187087 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185818, d187087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185818, d187087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185819 q = 0) : d187088 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185819, d187088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185819, d187088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185820 q = 0) : d187089 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185820, d187089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185820, d187089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185821 q = 0) : d187090 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185821, d187090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185821, d187090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17025 (p : Pattern) (selected : d185827 p = 0) : d187096 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185789 q = 0) : d187080 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185789, d187080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17015 q selected
    | true =>
      simp only [d185789, d187080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17017 q selected
  have h2 (q : Pattern) (selected : d185816 q = 0) : d187085 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185816, d187085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17022 q selected
    | true =>
      simp only [d185816, d187085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17023 q selected
  have h3 (q : Pattern) (selected : d185817 q = 0) : d187086 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185817, d187086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185817, d187086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185822 q = 0) : d187091 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185822, d187091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17024 q selected
    | true =>
      simp only [d185822, d187091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185823 q = 0) : d187092 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185823, d187092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185823, d187092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185824 q = 0) : d187093 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185824, d187093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185824, d187093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185825 q = 0) : d187094 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185825, d187094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185825, d187094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185826 q = 0) : d187095 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185826, d187095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185826, d187095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d185827 q = 0) : d187096 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185827, d187096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185827, d187096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro17026 (p : Pattern) (selected : d185832 p = 0) : d187084 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185783 q = 0) : d187074 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185783, d187074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17016 q selected
    | true =>
      simp only [d185783, d187074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185784 q = 0) : d187075 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185784, d187075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185784, d187075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185829 q = 0) : d187081 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185829, d187081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185829, d187081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185830 q = 0) : d187082 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185830, d187082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185830, d187082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185831 q = 0) : d187083 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185831, d187083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185831, d187083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185832 q = 0) : d187084 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185832, d187084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185832, d187084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17027 (p : Pattern) (selected : d185838 p = 0) : d187103 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185833 q = 0) : d187098 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185833, d187098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17026 q selected
    | true =>
      simp only [d185833, d187098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185834 q = 0) : d187099 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185834, d187099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185834, d187099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185835 q = 0) : d187100 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185835, d187100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185835, d187100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185836 q = 0) : d187101 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185836, d187101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185836, d187101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185837 q = 0) : d187102 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185837, d187102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185837, d187102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185838 q = 0) : d187103 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185838, d187103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185838, d187103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17028 (p : Pattern) (selected : d185844 p = 0) : d187109 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185613 q = 0) : d186934 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d185613, d186934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185613, d186934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16976 q selected
  have h2 (q : Pattern) (selected : d185614 q = 0) : d186935 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d185614, d186935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185614, d186935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d185623 q = 0) : d186944 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d185623, d186944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16976 q selected
    | true =>
      simp only [d185623, d186944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16979 q selected
  have h4 (q : Pattern) (selected : d185624 q = 0) : d186945 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d185624, d186945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185624, d186945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185625 q = 0) : d186946 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d185625, d186946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185625, d186946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185723 q = 0) : d187014 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d185723, d187014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16995 q selected
    | true =>
      simp only [d185723, d187014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17004 q selected
  have h7 (q : Pattern) (selected : d185736 q = 0) : d187027 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d185736, d187027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17005 q selected
    | true =>
      simp only [d185736, d187027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17006 q selected
  have h8 (q : Pattern) (selected : d185737 q = 0) : d187028 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d185737, d187028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185737, d187028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d185738 q = 0) : d187029 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d185738, d187029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d185738, d187029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d185739 q = 0) : d187030 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d185739, d187030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185739, d187030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185743 q = 0) : d187034 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d185743, d187034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185743, d187034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17007 q selected
  have h12 (q : Pattern) (selected : d185745 q = 0) : d187036 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d185745, d187036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185745, d187036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17008 q selected
  have h13 (q : Pattern) (selected : d185746 q = 0) : d187037 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d185746, d187037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d185746, d187037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d185747 q = 0) : d187038 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d185747, d187038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d185747, d187038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d185748 q = 0) : d187039 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d185748, d187039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d185748, d187039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d185749 q = 0) : d187040 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d185749, d187040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d185749, d187040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d185828 q = 0) : d187097 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d185828, d187097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185828, d187097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17025 q selected
  have h18 (q : Pattern) (selected : d185839 q = 0) : d187104 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d185839, d187104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185839, d187104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17027 q selected
  have h19 (q : Pattern) (selected : d185840 q = 0) : d187105 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d185840, d187105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d185840, d187105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d185841 q = 0) : d187106 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d185841, d187106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d185841, d187106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d185842 q = 0) : d187107 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d185842, d187107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d185842, d187107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d185843 q = 0) : d187108 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d185843, d187108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d185843, d187108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d185844 q = 0) : d187109 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d185844, d187109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d185844, d187109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro17029 (p : Pattern) (selected : d185850 p = 0) : d187115 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185845 q = 0) : d187110 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d185845, d187110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185845, d187110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17028 q selected
  have h2 (q : Pattern) (selected : d185846 q = 0) : d187111 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d185846, d187111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185846, d187111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185847 q = 0) : d187112 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d185847, d187112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185847, d187112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185848 q = 0) : d187113 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d185848, d187113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185848, d187113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185849 q = 0) : d187114 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d185849, d187114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185849, d187114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185850 q = 0) : d187115 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d185850, d187115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185850, d187115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17030 (p : Pattern) (selected : d185855 p = 0) : d187120 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10364 q = 0) : d101685 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d101685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6758 q selected
    | true =>
      simp only [d10364, d101685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10366 q = 0) : d101687 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, d101687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10366, d101687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d17153 q = 0) : d127855 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17153, d127855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17153, d127855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10371 q = 0) : d101692 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6759 q selected
    | true =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10373 q = 0) : d101694 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15548 q = 0) : d123547 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15548, d123547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15548, d123547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185855 q = 0) : d187120 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185855, d187120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185855, d187120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro17031 (p : Pattern) (selected : d185856 p = 0) : d187121 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10391 q = 0) : d101712 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10391, d101712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6762 q selected
    | true =>
      simp only [d10391, d101712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10393 q = 0) : d101714 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10393, d101714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10393, d101714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d17158 q = 0) : d127860 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17158, d127860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17158, d127860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185856 q = 0) : d187121 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185856, d187121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185856, d187121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro17032 (p : Pattern) (selected : d185866 p = 0) : d187131 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185857 q = 0) : d187122 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185857, d187122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17030 q selected
    | true =>
      simp only [d185857, d187122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17031 q selected
  have h2 (q : Pattern) (selected : d185858 q = 0) : d187123 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185858, d187123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185858, d187123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185859 q = 0) : d187124 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185859, d187124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185859, d187124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185860 q = 0) : d187125 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185860, d187125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17031 q selected
    | true =>
      simp only [d185860, d187125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185861 q = 0) : d187126 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185861, d187126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185861, d187126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185862 q = 0) : d187127 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185862, d187127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185862, d187127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185863 q = 0) : d187128 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185863, d187128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185863, d187128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185864 q = 0) : d187129 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185864, d187129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185864, d187129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d185865 q = 0) : d187130 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185865, d187130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185865, d187130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185866 q = 0) : d187131 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185866, d187131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d185866, d187131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro17033 (p : Pattern) (selected : d185870 p = 0) : d187135 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185860 q = 0) : d187125 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185860, d187125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17031 q selected
    | true =>
      simp only [d185860, d187125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185861 q = 0) : d187126 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185861, d187126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185861, d187126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185862 q = 0) : d187127 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185862, d187127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185862, d187127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185864 q = 0) : d187129 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185864, d187129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185864, d187129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185869 q = 0) : d187134 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185869, d187134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185869, d187134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185870 q = 0) : d187135 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185870, d187135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185870, d187135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17034 (p : Pattern) (selected : d185876 p = 0) : d187141 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185867 q = 0) : d187132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185867, d187132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17032 q selected
    | true =>
      simp only [d185867, d187132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185868 q = 0) : d187133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185868, d187133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185868, d187133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185871 q = 0) : d187136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185871, d187136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17033 q selected
    | true =>
      simp only [d185871, d187136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185872 q = 0) : d187137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185872, d187137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185872, d187137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185873 q = 0) : d187138 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185873, d187138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185873, d187138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185874 q = 0) : d187139 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185874, d187139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185874, d187139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185875 q = 0) : d187140 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185875, d187140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185875, d187140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185876 q = 0) : d187141 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185876, d187141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185876, d187141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro17035 (p : Pattern) (selected : d185880 p = 0) : d187145 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185871 q = 0) : d187136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185871, d187136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17033 q selected
    | true =>
      simp only [d185871, d187136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185872 q = 0) : d187137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185872, d187137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185872, d187137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185877 q = 0) : d187142 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185877, d187142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185877, d187142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185878 q = 0) : d187143 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185878, d187143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185878, d187143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185879 q = 0) : d187144 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185879, d187144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185879, d187144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185880 q = 0) : d187145 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185880, d187145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185880, d187145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17036 (p : Pattern) (selected : d185886 p = 0) : d187151 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185881 q = 0) : d187146 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185881, d187146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17034 q selected
    | true =>
      simp only [d185881, d187146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17035 q selected
  have h2 (q : Pattern) (selected : d185882 q = 0) : d187147 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185882, d187147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185882, d187147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185883 q = 0) : d187148 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185883, d187148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185883, d187148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185884 q = 0) : d187149 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185884, d187149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185884, d187149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185885 q = 0) : d187150 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185885, d187150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185885, d187150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185886 q = 0) : d187151 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185886, d187151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185886, d187151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17037 (p : Pattern) (selected : d185889 p = 0) : d187154 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185867 q = 0) : d187132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185867, d187132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17032 q selected
    | true =>
      simp only [d185867, d187132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185868 q = 0) : d187133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185868, d187133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185868, d187133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185871 q = 0) : d187136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185871, d187136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17033 q selected
    | true =>
      simp only [d185871, d187136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185872 q = 0) : d187137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185872, d187137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185872, d187137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185873 q = 0) : d187138 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185873, d187138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185873, d187138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185874 q = 0) : d187139 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185874, d187139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185874, d187139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185875 q = 0) : d187140 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185875, d187140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185875, d187140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185889 q = 0) : d187154 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185889, d187154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185889, d187154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17038 (p : Pattern) (selected : d185890 p = 0) : d187155 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185871 q = 0) : d187136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185871, d187136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17033 q selected
    | true =>
      simp only [d185871, d187136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185872 q = 0) : d187137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185872, d187137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185872, d187137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185877 q = 0) : d187142 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185877, d187142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185877, d187142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185878 q = 0) : d187143 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185878, d187143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185878, d187143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185879 q = 0) : d187144 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185879, d187144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185879, d187144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185890 q = 0) : d187155 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185890, d187155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185890, d187155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17039 (p : Pattern) (selected : d185896 p = 0) : d187161 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185881 q = 0) : d187146 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185881, d187146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17034 q selected
    | true =>
      simp only [d185881, d187146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17035 q selected
  have h2 (q : Pattern) (selected : d185882 q = 0) : d187147 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185882, d187147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185882, d187147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185883 q = 0) : d187148 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185883, d187148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185883, d187148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185884 q = 0) : d187149 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185884, d187149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185884, d187149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185885 q = 0) : d187150 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185885, d187150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185885, d187150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185891 q = 0) : d187156 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185891, d187156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17037 q selected
    | true =>
      simp only [d185891, d187156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17038 q selected
  have h7 (q : Pattern) (selected : d185892 q = 0) : d187157 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185892, d187157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185892, d187157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185893 q = 0) : d187158 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185893, d187158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185893, d187158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d185894 q = 0) : d187159 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185894, d187159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185894, d187159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185895 q = 0) : d187160 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185895, d187160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185895, d187160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185896 q = 0) : d187161 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185896, d187161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185896, d187161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro17040 (p : Pattern) (selected : d185901 p = 0) : d187166 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185867 q = 0) : d187132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185867, d187132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17032 q selected
    | true =>
      simp only [d185867, d187132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185868 q = 0) : d187133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185868, d187133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185868, d187133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185871 q = 0) : d187136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185871, d187136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17033 q selected
    | true =>
      simp only [d185871, d187136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185872 q = 0) : d187137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185872, d187137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185872, d187137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185873 q = 0) : d187138 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185873, d187138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185873, d187138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185874 q = 0) : d187139 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185874, d187139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185874, d187139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185900 q = 0) : d187165 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185900, d187165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185900, d187165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185901 q = 0) : d187166 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185901, d187166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185901, d187166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro17041 (p : Pattern) (selected : d185903 p = 0) : d187168 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185871 q = 0) : d187136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185871, d187136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17033 q selected
    | true =>
      simp only [d185871, d187136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185872 q = 0) : d187137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185872, d187137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185872, d187137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185877 q = 0) : d187142 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185877, d187142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185877, d187142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185878 q = 0) : d187143 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185878, d187143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185878, d187143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185902 q = 0) : d187167 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185902, d187167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185902, d187167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185903 q = 0) : d187168 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185903, d187168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185903, d187168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17042 (p : Pattern) (selected : d185910 p = 0) : d187175 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185867 q = 0) : d187132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185867, d187132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17032 q selected
    | true =>
      simp only [d185867, d187132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185868 q = 0) : d187133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185868, d187133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185868, d187133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185871 q = 0) : d187136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185871, d187136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17033 q selected
    | true =>
      simp only [d185871, d187136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185872 q = 0) : d187137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185872, d187137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185872, d187137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185873 q = 0) : d187138 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185873, d187138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185873, d187138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185908 q = 0) : d187173 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185908, d187173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185908, d187173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185909 q = 0) : d187174 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185909, d187174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185909, d187174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185910 q = 0) : d187175 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185910, d187175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185910, d187175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro17043 (p : Pattern) (selected : d185913 p = 0) : d187178 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185871 q = 0) : d187136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185871, d187136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17033 q selected
    | true =>
      simp only [d185871, d187136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185872 q = 0) : d187137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185872, d187137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185872, d187137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185877 q = 0) : d187142 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185877, d187142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185877, d187142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185911 q = 0) : d187176 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185911, d187176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185911, d187176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185912 q = 0) : d187177 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185912, d187177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185912, d187177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185913 q = 0) : d187178 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185913, d187178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185913, d187178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17044 (p : Pattern) (selected : d185917 p = 0) : d187182 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10343 q = 0) : d101664 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10343, d101664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6755 q selected
    | true =>
      simp only [d10343, d101664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10345 q = 0) : d101666 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10345, d101666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10345, d101666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d17225 q = 0) : d127927 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17225, d127927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17225, d127927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10353 q = 0) : d101674 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6756 q selected
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10355 q = 0) : d101676 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d13675 q = 0) : d113865 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13675, d113865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13675, d113865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185917 q = 0) : d187182 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185917, d187182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185917, d187182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro17045 (p : Pattern) (selected : d185921 p = 0) : d187186 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10371 q = 0) : d101692 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6759 q selected
    | true =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10373 q = 0) : d101694 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15548 q = 0) : d123547 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15548, d123547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15548, d123547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185921 q = 0) : d187186 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185921, d187186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185921, d187186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro17046 (p : Pattern) (selected : d185927 p = 0) : d187192 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185918 q = 0) : d187183 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185918, d187183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17044 q selected
    | true =>
      simp only [d185918, d187183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17030 q selected
  have h2 (q : Pattern) (selected : d185919 q = 0) : d187184 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185919, d187184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185919, d187184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185920 q = 0) : d187185 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185920, d187185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185920, d187185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185922 q = 0) : d187187 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185922, d187187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17030 q selected
    | true =>
      simp only [d185922, d187187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17045 q selected
  have h5 (q : Pattern) (selected : d185923 q = 0) : d187188 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185923, d187188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185923, d187188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185924 q = 0) : d187189 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185924, d187189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185924, d187189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185925 q = 0) : d187190 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185925, d187190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185925, d187190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185857 q = 0) : d187122 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185857, d187122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17030 q selected
    | true =>
      simp only [d185857, d187122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17031 q selected
  have h9 (q : Pattern) (selected : d185858 q = 0) : d187123 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185858, d187123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185858, d187123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185859 q = 0) : d187124 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185859, d187124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185859, d187124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185860 q = 0) : d187125 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185860, d187125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17031 q selected
    | true =>
      simp only [d185860, d187125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d185861 q = 0) : d187126 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185861, d187126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185861, d187126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d185862 q = 0) : d187127 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185862, d187127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185862, d187127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d185863 q = 0) : d187128 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185863, d187128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d185863, d187128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d185926 q = 0) : d187191 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185926, d187191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185926, d187191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d185927 q = 0) : d187192 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185927, d187192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d185927, d187192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro17047 (p : Pattern) (selected : d185933 p = 0) : d187198 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185928 q = 0) : d187193 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185928, d187193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17046 q selected
    | true =>
      simp only [d185928, d187193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185929 q = 0) : d187194 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185929, d187194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185929, d187194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185867 q = 0) : d187132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185867, d187132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17032 q selected
    | true =>
      simp only [d185867, d187132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185868 q = 0) : d187133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185868, d187133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185868, d187133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185930 q = 0) : d187195 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185930, d187195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185930, d187195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185931 q = 0) : d187196 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185931, d187196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185931, d187196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185932 q = 0) : d187197 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185932, d187197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185932, d187197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185933 q = 0) : d187198 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185933, d187198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185933, d187198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro17048 (p : Pattern) (selected : d185935 p = 0) : d187120 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10458 q = 0) : d101685 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10458, d101685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6772 q selected
    | true =>
      simp only [d10458, d101685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10460 q = 0) : d101687 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10460, d101687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10460, d101687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d17256 q = 0) : d127855 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17256, d127855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17256, d127855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10482 q = 0) : d101692 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10482, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6774 q selected
    | true =>
      simp only [d10482, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10484 q = 0) : d101694 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10484, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10484, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15654 q = 0) : d123547 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15654, d123547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15654, d123547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185935 q = 0) : d187120 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185935, d187120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185935, d187120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro17049 (p : Pattern) (selected : d185936 p = 0) : d187121 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10493 q = 0) : d101712 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10493, d101712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6776 q selected
    | true =>
      simp only [d10493, d101712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10495 q = 0) : d101714 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10495, d101714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10495, d101714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d17261 q = 0) : d127860 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17261, d127860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17261, d127860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185936 q = 0) : d187121 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185936, d187121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185936, d187121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro17050 (p : Pattern) (selected : d185946 p = 0) : d187131 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185937 q = 0) : d187122 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185937, d187122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17048 q selected
    | true =>
      simp only [d185937, d187122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17049 q selected
  have h2 (q : Pattern) (selected : d185938 q = 0) : d187123 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185938, d187123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185938, d187123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185939 q = 0) : d187124 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185939, d187124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185939, d187124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185940 q = 0) : d187125 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185940, d187125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17049 q selected
    | true =>
      simp only [d185940, d187125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185941 q = 0) : d187126 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185941, d187126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185941, d187126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185942 q = 0) : d187127 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185942, d187127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185942, d187127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185943 q = 0) : d187128 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185943, d187128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185943, d187128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185944 q = 0) : d187129 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185944, d187129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185944, d187129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d185945 q = 0) : d187130 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185945, d187130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185945, d187130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185946 q = 0) : d187131 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185946, d187131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d185946, d187131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro17051 (p : Pattern) (selected : d185950 p = 0) : d187135 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185940 q = 0) : d187125 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185940, d187125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17049 q selected
    | true =>
      simp only [d185940, d187125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185941 q = 0) : d187126 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185941, d187126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185941, d187126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185942 q = 0) : d187127 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185942, d187127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185942, d187127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185944 q = 0) : d187129 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185944, d187129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185944, d187129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185949 q = 0) : d187134 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185949, d187134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185949, d187134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185950 q = 0) : d187135 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185950, d187135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185950, d187135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17052 (p : Pattern) (selected : d185956 p = 0) : d187141 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185947 q = 0) : d187132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185947, d187132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17050 q selected
    | true =>
      simp only [d185947, d187132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185948 q = 0) : d187133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185948, d187133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185948, d187133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185951 q = 0) : d187136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185951, d187136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17051 q selected
    | true =>
      simp only [d185951, d187136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185952 q = 0) : d187137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185952, d187137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185952, d187137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185953 q = 0) : d187138 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185953, d187138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185953, d187138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185954 q = 0) : d187139 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185954, d187139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185954, d187139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185955 q = 0) : d187140 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185955, d187140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185955, d187140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185956 q = 0) : d187141 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185956, d187141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185956, d187141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro17053 (p : Pattern) (selected : d185960 p = 0) : d187145 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185951 q = 0) : d187136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185951, d187136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17051 q selected
    | true =>
      simp only [d185951, d187136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185952 q = 0) : d187137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185952, d187137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185952, d187137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185957 q = 0) : d187142 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185957, d187142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185957, d187142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185958 q = 0) : d187143 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185958, d187143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185958, d187143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185959 q = 0) : d187144 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185959, d187144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185959, d187144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185960 q = 0) : d187145 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185960, d187145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185960, d187145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17054 (p : Pattern) (selected : d185966 p = 0) : d187204 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185867 q = 0) : d187132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185867, d187132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17032 q selected
    | true =>
      simp only [d185867, d187132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185868 q = 0) : d187133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185868, d187133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185868, d187133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185963 q = 0) : d187201 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185963, d187201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185963, d187201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185964 q = 0) : d187202 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185964, d187202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185964, d187202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185965 q = 0) : d187203 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185965, d187203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185965, d187203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185966 q = 0) : d187204 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185966, d187204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185966, d187204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17055 (p : Pattern) (selected : d185972 p = 0) : d187210 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185904 q = 0) : d187169 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185904, d187169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17040 q selected
    | true =>
      simp only [d185904, d187169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17041 q selected
  have h2 (q : Pattern) (selected : d185905 q = 0) : d187170 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185905, d187170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185905, d187170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185906 q = 0) : d187171 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185906, d187171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185906, d187171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185907 q = 0) : d187172 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185907, d187172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185907, d187172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185914 q = 0) : d187179 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185914, d187179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17042 q selected
    | true =>
      simp only [d185914, d187179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17043 q selected
  have h6 (q : Pattern) (selected : d185915 q = 0) : d187180 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185915, d187180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185915, d187180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185916 q = 0) : d187181 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185916, d187181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185916, d187181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185934 q = 0) : d187199 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185934, d187199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17047 q selected
    | true =>
      simp only [d185934, d187199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17034 q selected
  have h9 (q : Pattern) (selected : d185961 q = 0) : d187146 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185961, d187146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17052 q selected
    | true =>
      simp only [d185961, d187146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17053 q selected
  have h10 (q : Pattern) (selected : d185962 q = 0) : d187200 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185962, d187200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d185962, d187200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185967 q = 0) : d187205 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185967, d187205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17054 q selected
    | true =>
      simp only [d185967, d187205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d185968 q = 0) : d187206 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185968, d187206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d185968, d187206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d185969 q = 0) : d187207 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185969, d187207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d185969, d187207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d185970 q = 0) : d187208 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185970, d187208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185970, d187208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d185971 q = 0) : d187209 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185971, d187209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185971, d187209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d185972 q = 0) : d187210 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185972, d187210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185972, d187210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro17056 (p : Pattern) (selected : d185973 p = 0) : d187211 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185867 q = 0) : d187132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185867, d187132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17032 q selected
    | true =>
      simp only [d185867, d187132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185868 q = 0) : d187133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185868, d187133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185868, d187133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185871 q = 0) : d187136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185871, d187136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17033 q selected
    | true =>
      simp only [d185871, d187136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185872 q = 0) : d187137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185872, d187137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185872, d187137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185873 q = 0) : d187138 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185873, d187138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185873, d187138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185874 q = 0) : d187139 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185874, d187139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185874, d187139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185900 q = 0) : d187165 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185900, d187165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185900, d187165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185973 q = 0) : d187211 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185973, d187211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185973, d187211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17057 (p : Pattern) (selected : d185974 p = 0) : d187212 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185871 q = 0) : d187136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185871, d187136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17033 q selected
    | true =>
      simp only [d185871, d187136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185872 q = 0) : d187137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185872, d187137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185872, d187137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185877 q = 0) : d187142 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185877, d187142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185877, d187142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185878 q = 0) : d187143 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185878, d187143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185878, d187143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185902 q = 0) : d187167 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185902, d187167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185902, d187167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185974 q = 0) : d187212 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185974, d187212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185974, d187212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17058 (p : Pattern) (selected : d185979 p = 0) : d187217 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185867 q = 0) : d187132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185867, d187132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17032 q selected
    | true =>
      simp only [d185867, d187132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185868 q = 0) : d187133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185868, d187133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185868, d187133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185871 q = 0) : d187136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185871, d187136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17033 q selected
    | true =>
      simp only [d185871, d187136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185872 q = 0) : d187137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185872, d187137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185872, d187137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185873 q = 0) : d187138 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185873, d187138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185873, d187138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185908 q = 0) : d187173 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185908, d187173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185908, d187173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185909 q = 0) : d187174 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185909, d187174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185909, d187174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185979 q = 0) : d187217 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185979, d187217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185979, d187217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17059 (p : Pattern) (selected : d185980 p = 0) : d187218 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185871 q = 0) : d187136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185871, d187136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17033 q selected
    | true =>
      simp only [d185871, d187136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185872 q = 0) : d187137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185872, d187137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185872, d187137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185877 q = 0) : d187142 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185877, d187142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185877, d187142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185911 q = 0) : d187176 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185911, d187176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185911, d187176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185912 q = 0) : d187177 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185912, d187177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185912, d187177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185980 q = 0) : d187218 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185980, d187218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185980, d187218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17060 (p : Pattern) (selected : d185984 p = 0) : d187222 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185928 q = 0) : d187193 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185928, d187193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17046 q selected
    | true =>
      simp only [d185928, d187193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185929 q = 0) : d187194 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185929, d187194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185929, d187194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185867 q = 0) : d187132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185867, d187132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17032 q selected
    | true =>
      simp only [d185867, d187132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185868 q = 0) : d187133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185868, d187133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185868, d187133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185930 q = 0) : d187195 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185930, d187195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185930, d187195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185931 q = 0) : d187196 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185931, d187196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185931, d187196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185932 q = 0) : d187197 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185932, d187197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185932, d187197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185984 q = 0) : d187222 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185984, d187222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185984, d187222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17061 (p : Pattern) (selected : d185986 p = 0) : d187154 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185947 q = 0) : d187132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185947, d187132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17050 q selected
    | true =>
      simp only [d185947, d187132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185948 q = 0) : d187133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185948, d187133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185948, d187133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185951 q = 0) : d187136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185951, d187136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17051 q selected
    | true =>
      simp only [d185951, d187136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185952 q = 0) : d187137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185952, d187137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185952, d187137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185953 q = 0) : d187138 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185953, d187138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185953, d187138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185954 q = 0) : d187139 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185954, d187139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185954, d187139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185955 q = 0) : d187140 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185955, d187140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185955, d187140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185986 q = 0) : d187154 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185986, d187154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185986, d187154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17062 (p : Pattern) (selected : d185987 p = 0) : d187155 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185951 q = 0) : d187136 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185951, d187136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17051 q selected
    | true =>
      simp only [d185951, d187136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185952 q = 0) : d187137 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185952, d187137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185952, d187137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185957 q = 0) : d187142 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185957, d187142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185957, d187142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185958 q = 0) : d187143 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185958, d187143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185958, d187143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185959 q = 0) : d187144 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185959, d187144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185959, d187144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185987 q = 0) : d187155 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185987, d187155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185987, d187155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17063 (p : Pattern) (selected : d185990 p = 0) : d187225 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185867 q = 0) : d187132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185867, d187132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17032 q selected
    | true =>
      simp only [d185867, d187132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185868 q = 0) : d187133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185868, d187133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185868, d187133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185963 q = 0) : d187201 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185963, d187201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185963, d187201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185964 q = 0) : d187202 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185964, d187202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185964, d187202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185965 q = 0) : d187203 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185965, d187203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185965, d187203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185990 q = 0) : d187225 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185990, d187225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185990, d187225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17064 (p : Pattern) (selected : d185996 p = 0) : d187231 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185904 q = 0) : d187169 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185904, d187169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17040 q selected
    | true =>
      simp only [d185904, d187169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17041 q selected
  have h2 (q : Pattern) (selected : d185905 q = 0) : d187170 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185905, d187170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185905, d187170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185906 q = 0) : d187171 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185906, d187171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185906, d187171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185907 q = 0) : d187172 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185907, d187172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185907, d187172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185914 q = 0) : d187179 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185914, d187179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17042 q selected
    | true =>
      simp only [d185914, d187179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17043 q selected
  have h6 (q : Pattern) (selected : d185915 q = 0) : d187180 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185915, d187180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185915, d187180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185916 q = 0) : d187181 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185916, d187181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185916, d187181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185934 q = 0) : d187199 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185934, d187199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17047 q selected
    | true =>
      simp only [d185934, d187199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17034 q selected
  have h9 (q : Pattern) (selected : d185961 q = 0) : d187146 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185961, d187146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17052 q selected
    | true =>
      simp only [d185961, d187146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17053 q selected
  have h10 (q : Pattern) (selected : d185962 q = 0) : d187200 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185962, d187200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d185962, d187200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185967 q = 0) : d187205 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185967, d187205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17054 q selected
    | true =>
      simp only [d185967, d187205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d185968 q = 0) : d187206 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185968, d187206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d185968, d187206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d185969 q = 0) : d187207 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185969, d187207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d185969, d187207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d185970 q = 0) : d187208 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185970, d187208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185970, d187208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d185971 q = 0) : d187209 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185971, d187209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185971, d187209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d185975 q = 0) : d187213 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185975, d187213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17056 q selected
    | true =>
      simp only [d185975, d187213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17057 q selected
  have h17 (q : Pattern) (selected : d185976 q = 0) : d187214 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185976, d187214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185976, d187214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d185977 q = 0) : d187215 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185977, d187215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d185977, d187215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d185978 q = 0) : d187216 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185978, d187216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185978, d187216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d185981 q = 0) : d187219 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185981, d187219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17058 q selected
    | true =>
      simp only [d185981, d187219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17059 q selected
  have h21 (q : Pattern) (selected : d185982 q = 0) : d187220 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185982, d187220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185982, d187220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d185983 q = 0) : d187221 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185983, d187221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d185983, d187221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d185985 q = 0) : d187223 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185985, d187223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17060 q selected
    | true =>
      simp only [d185985, d187223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17037 q selected
  have h24 (q : Pattern) (selected : d185988 q = 0) : d187156 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185988, d187156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17061 q selected
    | true =>
      simp only [d185988, d187156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17062 q selected
  have h25 (q : Pattern) (selected : d185989 q = 0) : d187224 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185989, d187224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d185989, d187224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d185991 q = 0) : d187226 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185991, d187226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17063 q selected
    | true =>
      simp only [d185991, d187226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d185992 q = 0) : d187227 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185992, d187227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d185992, d187227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d185993 q = 0) : d187228 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185993, d187228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d185993, d187228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d185994 q = 0) : d187229 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185994, d187229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d185994, d187229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d185995 q = 0) : d187230 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185995, d187230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d185995, d187230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d185996 q = 0) : d187231 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185996, d187231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d185996, d187231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro17065 (p : Pattern) (selected : d186003 p = 0) : d187238 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185881 q = 0) : d187146 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185881, d187146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17034 q selected
    | true =>
      simp only [d185881, d187146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17035 q selected
  have h2 (q : Pattern) (selected : d185882 q = 0) : d187147 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185882, d187147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185882, d187147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185883 q = 0) : d187148 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185883, d187148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185883, d187148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185884 q = 0) : d187149 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185884, d187149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185884, d187149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185885 q = 0) : d187150 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185885, d187150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185885, d187150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185998 q = 0) : d187233 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185998, d187233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17035 q selected
    | true =>
      simp only [d185998, d187233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185999 q = 0) : d187234 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185999, d187234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185999, d187234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d186000 q = 0) : d187235 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d186000, d187235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d186000, d187235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d186001 q = 0) : d187236 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d186001, d187236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186001, d187236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d186002 q = 0) : d187237 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d186002, d187237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186002, d187237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d186003 q = 0) : d187238 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d186003, d187238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d186003, d187238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro17066 (p : Pattern) (selected : d186009 p = 0) : d187244 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185998 q = 0) : d187233 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185998, d187233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17035 q selected
    | true =>
      simp only [d185998, d187233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185999 q = 0) : d187234 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185999, d187234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185999, d187234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d186000 q = 0) : d187235 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d186000, d187235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d186000, d187235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d186001 q = 0) : d187236 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d186001, d187236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186001, d187236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d186002 q = 0) : d187237 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d186002, d187237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186002, d187237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d186004 q = 0) : d187239 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d186004, d187239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17038 q selected
    | true =>
      simp only [d186004, d187239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d186005 q = 0) : d187240 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d186005, d187240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186005, d187240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d186006 q = 0) : d187241 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d186006, d187241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d186006, d187241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d186007 q = 0) : d187242 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d186007, d187242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186007, d187242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d186008 q = 0) : d187243 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d186008, d187243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186008, d187243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d186009 q = 0) : d187244 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d186009, d187244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d186009, d187244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro17067 (p : Pattern) (selected : d186016 p = 0) : d187251 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185985 q = 0) : d187223 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185985, d187223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17060 q selected
    | true =>
      simp only [d185985, d187223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17037 q selected
  have h2 (q : Pattern) (selected : d185988 q = 0) : d187156 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185988, d187156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17061 q selected
    | true =>
      simp only [d185988, d187156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17062 q selected
  have h3 (q : Pattern) (selected : d185989 q = 0) : d187224 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185989, d187224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185989, d187224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185991 q = 0) : d187226 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185991, d187226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17063 q selected
    | true =>
      simp only [d185991, d187226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185992 q = 0) : d187227 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185992, d187227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185992, d187227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185993 q = 0) : d187228 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185993, d187228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185993, d187228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d186014 q = 0) : d187249 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d186014, d187249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186014, d187249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d186015 q = 0) : d187250 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d186015, d187250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186015, d187250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d186016 q = 0) : d187251 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d186016, d187251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186016, d187251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro17068 (p : Pattern) (selected : d186018 p = 0) : d187253 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d186004 q = 0) : d187239 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d186004, d187239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17038 q selected
    | true =>
      simp only [d186004, d187239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d186005 q = 0) : d187240 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d186005, d187240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186005, d187240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d186006 q = 0) : d187241 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d186006, d187241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d186006, d187241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d186007 q = 0) : d187242 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d186007, d187242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186007, d187242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d186008 q = 0) : d187243 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d186008, d187243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186008, d187243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d186018 q = 0) : d187253 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d186018, d187253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186018, d187253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17069 (p : Pattern) (selected : d186024 p = 0) : d187259 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d17369 q = 0) : d128031 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17369, d128031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17369, d128031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6755 q selected
  have h2 (q : Pattern) (selected : d10343 q = 0) : d101664 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10343, d101664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6755 q selected
    | true =>
      simp only [d10343, d101664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d17370 q = 0) : d128032 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17370, d128032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d17370, d128032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10345 q = 0) : d101666 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10345, d101666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10345, d101666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17371 q = 0) : d128033 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17371, d128033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17371, d128033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13813 q = 0) : d113965 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6756 q selected
  have h7 (q : Pattern) (selected : d10353 q = 0) : d101674 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6756 q selected
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d13814 q = 0) : d113966 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10355 q = 0) : d101676 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d13815 q = 0) : d113967 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13815, d113967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d13815, d113967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d186024 q = 0) : d187259 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d186024, d187259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d186024, d187259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro17070 (p : Pattern) (selected : d186025 p = 0) : d187260 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d17376 q = 0) : d128038 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17376, d128038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17376, d128038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6758 q selected
  have h2 (q : Pattern) (selected : d10364 q = 0) : d101685 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d101685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6758 q selected
    | true =>
      simp only [d10364, d101685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d17377 q = 0) : d128039 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17377, d128039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d17377, d128039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10366 q = 0) : d101687 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, d101687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10366, d101687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17378 q = 0) : d128040 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17378, d128040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17378, d128040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15775 q = 0) : d123728 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15775, d123728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15775, d123728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6759 q selected
  have h7 (q : Pattern) (selected : d10371 q = 0) : d101692 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6759 q selected
    | true =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15776 q = 0) : d123729 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15776, d123729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15776, d123729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10373 q = 0) : d101694 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15777 q = 0) : d123730 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15777, d123730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15777, d123730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d186025 q = 0) : d187260 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d186025, d187260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d186025, d187260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro17071 (p : Pattern) (selected : d186029 p = 0) : d187264 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d15775 q = 0) : d123728 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15775, d123728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15775, d123728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6759 q selected
  have h2 (q : Pattern) (selected : d10371 q = 0) : d101692 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6759 q selected
    | true =>
      simp only [d10371, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15776 q = 0) : d123729 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15776, d123729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15776, d123729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10373 q = 0) : d101694 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10373, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15777 q = 0) : d123730 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15777, d123730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15777, d123730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d186029 q = 0) : d187264 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d186029, d187264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d186029, d187264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17072 (p : Pattern) (selected : d186034 p = 0) : d187269 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d17391 q = 0) : d128053 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17391, d128053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17391, d128053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6762 q selected
  have h2 (q : Pattern) (selected : d10391 q = 0) : d101712 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10391, d101712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6762 q selected
    | true =>
      simp only [d10391, d101712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d17392 q = 0) : d128054 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17392, d128054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d17392, d128054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10393 q = 0) : d101714 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10393, d101714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10393, d101714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17393 q = 0) : d128055 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17393, d128055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17393, d128055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d186034 q = 0) : d187269 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d186034, d187269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d186034, d187269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17073 (p : Pattern) (selected : d186043 p = 0) : d187278 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d186026 q = 0) : d187261 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d186026, d187261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17069 q selected
    | true =>
      simp only [d186026, d187261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17070 q selected
  have h2 (q : Pattern) (selected : d186027 q = 0) : d187262 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d186027, d187262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186027, d187262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d186028 q = 0) : d187263 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d186028, d187263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186028, d187263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d186030 q = 0) : d187265 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d186030, d187265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17070 q selected
    | true =>
      simp only [d186030, d187265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17071 q selected
  have h5 (q : Pattern) (selected : d186031 q = 0) : d187266 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d186031, d187266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186031, d187266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d186032 q = 0) : d187267 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d186032, d187267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186032, d187267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d186033 q = 0) : d187268 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d186033, d187268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d186033, d187268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d186035 q = 0) : d187270 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d186035, d187270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17070 q selected
    | true =>
      simp only [d186035, d187270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17072 q selected
  have h9 (q : Pattern) (selected : d186036 q = 0) : d187271 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d186036, d187271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186036, d187271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d186037 q = 0) : d187272 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d186037, d187272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186037, d187272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d186038 q = 0) : d187273 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d186038, d187273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17072 q selected
    | true =>
      simp only [d186038, d187273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d186039 q = 0) : d187274 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d186039, d187274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186039, d187274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d186040 q = 0) : d187275 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d186040, d187275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186040, d187275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d186041 q = 0) : d187276 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d186041, d187276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d186041, d187276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d186042 q = 0) : d187277 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d186042, d187277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d186042, d187277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d186043 q = 0) : d187278 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d186043, d187278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d186043, d187278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro17074 (p : Pattern) (selected : d186048 p = 0) : d187283 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d186035 q = 0) : d187270 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d186035, d187270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17070 q selected
    | true =>
      simp only [d186035, d187270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17072 q selected
  have h2 (q : Pattern) (selected : d186036 q = 0) : d187271 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d186036, d187271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186036, d187271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d186037 q = 0) : d187272 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d186037, d187272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186037, d187272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d186038 q = 0) : d187273 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d186038, d187273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17072 q selected
    | true =>
      simp only [d186038, d187273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d186039 q = 0) : d187274 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d186039, d187274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186039, d187274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d186040 q = 0) : d187275 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d186040, d187275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186040, d187275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d186041 q = 0) : d187276 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d186041, d187276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d186041, d187276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d186046 q = 0) : d187281 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d186046, d187281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d186046, d187281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d186047 q = 0) : d187282 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d186047, d187282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d186047, d187282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d186048 q = 0) : d187283 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d186048, d187283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d186048, d187283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro17075 (p : Pattern) (selected : d186054 p = 0) : d187289 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d186044 q = 0) : d187279 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d186044, d187279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17073 q selected
    | true =>
      simp only [d186044, d187279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d186045 q = 0) : d187280 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d186045, d187280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186045, d187280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d186049 q = 0) : d187284 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d186049, d187284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17074 q selected
    | true =>
      simp only [d186049, d187284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d186050 q = 0) : d187285 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d186050, d187285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186050, d187285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d186051 q = 0) : d187286 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d186051, d187286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d186051, d187286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d186052 q = 0) : d187287 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d186052, d187287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d186052, d187287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d186053 q = 0) : d187288 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d186053, d187288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d186053, d187288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d186054 q = 0) : d187289 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d186054, d187289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d186054, d187289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17076 (p : Pattern) (selected : d186056 p = 0) : d187291 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d186038 q = 0) : d187273 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d186038, d187273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17072 q selected
    | true =>
      simp only [d186038, d187273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d186039 q = 0) : d187274 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d186039, d187274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186039, d187274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d186040 q = 0) : d187275 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d186040, d187275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186040, d187275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d186046 q = 0) : d187281 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d186046, d187281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d186046, d187281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d186055 q = 0) : d187290 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d186055, d187290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d186055, d187290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d186056 q = 0) : d187291 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d186056, d187291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d186056, d187291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17077 (p : Pattern) (selected : d186062 p = 0) : d187297 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d186049 q = 0) : d187284 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d186049, d187284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17074 q selected
    | true =>
      simp only [d186049, d187284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d186050 q = 0) : d187285 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d186050, d187285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186050, d187285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d186057 q = 0) : d187292 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d186057, d187292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17076 q selected
    | true =>
      simp only [d186057, d187292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d186058 q = 0) : d187293 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d186058, d187293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186058, d187293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d186059 q = 0) : d187294 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d186059, d187294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d186059, d187294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d186060 q = 0) : d187295 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d186060, d187295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d186060, d187295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d186061 q = 0) : d187296 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d186061, d187296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d186061, d187296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d186062 q = 0) : d187297 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d186062, d187297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d186062, d187297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17078 (p : Pattern) (selected : d186064 p = 0) : d187260 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d17430 q = 0) : d128038 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17430, d128038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17430, d128038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6772 q selected
  have h2 (q : Pattern) (selected : d10458 q = 0) : d101685 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10458, d101685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6772 q selected
    | true =>
      simp only [d10458, d101685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d17431 q = 0) : d128039 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17431, d128039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d17431, d128039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10460 q = 0) : d101687 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10460, d101687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10460, d101687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17432 q = 0) : d128040 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17432, d128040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17432, d128040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15835 q = 0) : d123728 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15835, d123728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15835, d123728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6774 q selected
  have h7 (q : Pattern) (selected : d10482 q = 0) : d101692 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10482, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6774 q selected
    | true =>
      simp only [d10482, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15836 q = 0) : d123729 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15836, d123729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15836, d123729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10484 q = 0) : d101694 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10484, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10484, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15837 q = 0) : d123730 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15837, d123730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15837, d123730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d186064 q = 0) : d187260 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d186064, d187260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d186064, d187260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro17079 (p : Pattern) (selected : d186065 p = 0) : d187269 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d17437 q = 0) : d128053 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17437, d128053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17437, d128053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6776 q selected
  have h2 (q : Pattern) (selected : d10493 q = 0) : d101712 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10493, d101712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6776 q selected
    | true =>
      simp only [d10493, d101712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d17438 q = 0) : d128054 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17438, d128054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d17438, d128054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10495 q = 0) : d101714 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10495, d101714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10495, d101714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17439 q = 0) : d128055 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17439, d128055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17439, d128055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d186065 q = 0) : d187269 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d186065, d187269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d186065, d187269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17080 (p : Pattern) (selected : d186075 p = 0) : d187283 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d186066 q = 0) : d187270 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d186066, d187270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17078 q selected
    | true =>
      simp only [d186066, d187270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17079 q selected
  have h2 (q : Pattern) (selected : d186067 q = 0) : d187271 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d186067, d187271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186067, d187271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d186068 q = 0) : d187272 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d186068, d187272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186068, d187272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d186069 q = 0) : d187273 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d186069, d187273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17079 q selected
    | true =>
      simp only [d186069, d187273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d186070 q = 0) : d187274 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d186070, d187274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186070, d187274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d186071 q = 0) : d187275 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d186071, d187275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186071, d187275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d186072 q = 0) : d187276 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d186072, d187276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d186072, d187276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d186073 q = 0) : d187281 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d186073, d187281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d186073, d187281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d186074 q = 0) : d187282 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d186074, d187282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d186074, d187282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d186075 q = 0) : d187283 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d186075, d187283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d186075, d187283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro17081 (p : Pattern) (selected : d186079 p = 0) : d187291 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d186069 q = 0) : d187273 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d186069, d187273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17079 q selected
    | true =>
      simp only [d186069, d187273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d186070 q = 0) : d187274 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d186070, d187274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186070, d187274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d186071 q = 0) : d187275 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d186071, d187275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186071, d187275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d186073 q = 0) : d187281 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d186073, d187281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d186073, d187281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d186078 q = 0) : d187290 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d186078, d187290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d186078, d187290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d186079 q = 0) : d187291 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d186079, d187291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d186079, d187291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17082 (p : Pattern) (selected : d186085 p = 0) : d187297 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d186076 q = 0) : d187284 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d186076, d187284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17080 q selected
    | true =>
      simp only [d186076, d187284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d186077 q = 0) : d187285 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d186077, d187285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186077, d187285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d186080 q = 0) : d187292 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d186080, d187292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17081 q selected
    | true =>
      simp only [d186080, d187292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d186081 q = 0) : d187293 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d186081, d187293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186081, d187293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d186082 q = 0) : d187294 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d186082, d187294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d186082, d187294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d186083 q = 0) : d187295 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d186083, d187295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d186083, d187295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d186084 q = 0) : d187296 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d186084, d187296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d186084, d187296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d186085 q = 0) : d187297 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d186085, d187297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d186085, d187297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17083 (p : Pattern) (selected : d186089 p = 0) : d187302 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d186080 q = 0) : d187292 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d186080, d187292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17081 q selected
    | true =>
      simp only [d186080, d187292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d186081 q = 0) : d187293 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d186081, d187293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186081, d187293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d186086 q = 0) : d187299 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d186086, d187299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d186086, d187299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d186087 q = 0) : d187300 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d186087, d187300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d186087, d187300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d186088 q = 0) : d187301 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d186088, d187301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d186088, d187301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d186089 q = 0) : d187302 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d186089, d187302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d186089, d187302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17084 (p : Pattern) (selected : d186095 p = 0) : d187308 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d186049 q = 0) : d187284 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d186049, d187284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17074 q selected
    | true =>
      simp only [d186049, d187284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d186050 q = 0) : d187285 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d186050, d187285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186050, d187285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d186092 q = 0) : d187305 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d186092, d187305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d186092, d187305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d186093 q = 0) : d187306 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d186093, d187306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d186093, d187306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d186094 q = 0) : d187307 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d186094, d187307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d186094, d187307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d186095 q = 0) : d187308 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d186095, d187308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d186095, d187308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17085 (p : Pattern) (selected : d186101 p = 0) : d187314 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d186063 q = 0) : d187298 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d186063, d187298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17075 q selected
    | true =>
      simp only [d186063, d187298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17077 q selected
  have h2 (q : Pattern) (selected : d186090 q = 0) : d187303 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d186090, d187303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17082 q selected
    | true =>
      simp only [d186090, d187303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17083 q selected
  have h3 (q : Pattern) (selected : d186091 q = 0) : d187304 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d186091, d187304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d186091, d187304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d186096 q = 0) : d187309 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d186096, d187309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17084 q selected
    | true =>
      simp only [d186096, d187309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d186097 q = 0) : d187310 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d186097, d187310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d186097, d187310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d186098 q = 0) : d187311 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d186098, d187311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d186098, d187311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d186099 q = 0) : d187312 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d186099, d187312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186099, d187312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d186100 q = 0) : d187313 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d186100, d187313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186100, d187313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d186101 q = 0) : d187314 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d186101, d187314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186101, d187314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro17086 (p : Pattern) (selected : d186106 p = 0) : d187302 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d186057 q = 0) : d187292 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d186057, d187292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17076 q selected
    | true =>
      simp only [d186057, d187292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d186058 q = 0) : d187293 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d186058, d187293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186058, d187293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d186103 q = 0) : d187299 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d186103, d187299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d186103, d187299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d186104 q = 0) : d187300 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d186104, d187300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d186104, d187300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d186105 q = 0) : d187301 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d186105, d187301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d186105, d187301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d186106 q = 0) : d187302 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d186106, d187302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d186106, d187302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17087 (p : Pattern) (selected : d186112 p = 0) : d187321 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d186107 q = 0) : d187316 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d186107, d187316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17086 q selected
    | true =>
      simp only [d186107, d187316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d186108 q = 0) : d187317 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d186108, d187317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186108, d187317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d186109 q = 0) : d187318 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d186109, d187318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d186109, d187318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d186110 q = 0) : d187319 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d186110, d187319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186110, d187319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d186111 q = 0) : d187320 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d186111, d187320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186111, d187320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d186112 q = 0) : d187321 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d186112, d187321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186112, d187321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17088 (p : Pattern) (selected : d186118 p = 0) : d187327 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d185887 q = 0) : d187152 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d185887, d187152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185887, d187152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17036 q selected
  have h2 (q : Pattern) (selected : d185888 q = 0) : d187153 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d185888, d187153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185888, d187153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d185897 q = 0) : d187162 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d185897, d187162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17036 q selected
    | true =>
      simp only [d185897, d187162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17039 q selected
  have h4 (q : Pattern) (selected : d185898 q = 0) : d187163 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d185898, d187163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185898, d187163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185899 q = 0) : d187164 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d185899, d187164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185899, d187164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185997 q = 0) : d187232 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d185997, d187232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17055 q selected
    | true =>
      simp only [d185997, d187232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17064 q selected
  have h7 (q : Pattern) (selected : d186010 q = 0) : d187245 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d186010, d187245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17065 q selected
    | true =>
      simp only [d186010, d187245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17066 q selected
  have h8 (q : Pattern) (selected : d186011 q = 0) : d187246 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d186011, d187246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d186011, d187246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d186012 q = 0) : d187247 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d186012, d187247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d186012, d187247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d186013 q = 0) : d187248 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d186013, d187248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d186013, d187248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d186017 q = 0) : d187252 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d186017, d187252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186017, d187252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17067 q selected
  have h12 (q : Pattern) (selected : d186019 q = 0) : d187254 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d186019, d187254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186019, d187254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17068 q selected
  have h13 (q : Pattern) (selected : d186020 q = 0) : d187255 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d186020, d187255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d186020, d187255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d186021 q = 0) : d187256 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d186021, d187256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d186021, d187256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d186022 q = 0) : d187257 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d186022, d187257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d186022, d187257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d186023 q = 0) : d187258 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d186023, d187258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d186023, d187258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d186102 q = 0) : d187315 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d186102, d187315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186102, d187315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17085 q selected
  have h18 (q : Pattern) (selected : d186113 q = 0) : d187322 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d186113, d187322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186113, d187322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17087 q selected
  have h19 (q : Pattern) (selected : d186114 q = 0) : d187323 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d186114, d187323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d186114, d187323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d186115 q = 0) : d187324 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d186115, d187324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d186115, d187324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d186116 q = 0) : d187325 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d186116, d187325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d186116, d187325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d186117 q = 0) : d187326 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d186117, d187326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d186117, d187326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d186118 q = 0) : d187327 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d186118, d187327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d186118, d187327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro17089 (p : Pattern) (selected : d186124 p = 0) : d187333 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d186119 q = 0) : d187328 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d186119, d187328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186119, d187328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17088 q selected
  have h2 (q : Pattern) (selected : d186120 q = 0) : d187329 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d186120, d187329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186120, d187329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d186121 q = 0) : d187330 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d186121, d187330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186121, d187330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d186122 q = 0) : d187331 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d186122, d187331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186122, d187331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d186123 q = 0) : d187332 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d186123, d187332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186123, d187332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d186124 q = 0) : d187333 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d186124, d187333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186124, d187333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17090 (p : Pattern) (selected : d186130 p = 0) : d187339 p = 1 := by
  have h0 (q : Pattern) (selected : d185043 q = 0) : d186476 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d185043, d186476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16819 q selected
    | true =>
      simp only [d185043, d186476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16851 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d185306 q = 0) : d186683 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d185306, d186683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185306, d186683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16909 q selected
  have h3 (q : Pattern) (selected : d185307 q = 0) : d186684 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d185307, d186684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185307, d186684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185578 q = 0) : d186899 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d185578, d186899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185578, d186899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16969 q selected
  have h5 (q : Pattern) (selected : d185579 q = 0) : d186900 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d185579, d186900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185579, d186900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185580 q = 0) : d186901 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d185580, d186901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185580, d186901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185851 q = 0) : d187116 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d185851, d187116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185851, d187116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17029 q selected
  have h8 (q : Pattern) (selected : d185852 q = 0) : d187117 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d185852, d187117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185852, d187117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d185853 q = 0) : d187118 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d185853, d187118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185853, d187118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185854 q = 0) : d187119 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d185854, d187119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185854, d187119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d186125 q = 0) : d187334 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d186125, d187334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d186125, d187334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17089 q selected
  have h12 (q : Pattern) (selected : d186126 q = 0) : d187335 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d186126, d187335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d186126, d187335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d186127 q = 0) : d187336 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d186127, d187336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d186127, d187336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d186128 q = 0) : d187337 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d186128, d187337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d186128, d187337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d186129 q = 0) : d187338 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d186129, d187338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d186129, d187338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d186130 q = 0) : d187339 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d186130, d187339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d186130, d187339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro17091 (p : Pattern) (selected : d186136 p = 0) : d187345 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d186131 q = 0) : d187340 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d186131, d187340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17090 q selected
    | true =>
      simp only [d186131, d187340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d186132 q = 0) : d187341 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d186132, d187341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d186132, d187341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d186133 q = 0) : d187342 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d186133, d187342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d186133, d187342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d186134 q = 0) : d187343 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d186134, d187343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d186134, d187343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d186135 q = 0) : d187344 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d186135, d187344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d186135, d187344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d186136 q = 0) : d187345 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d186136, d187345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d186136, d187345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17092 (p : Pattern) (selected : d186142 p = 0) : d187351 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d186137 q = 0) : d187346 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d186137, d187346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17091 q selected
    | true =>
      simp only [d186137, d187346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d186138 q = 0) : d187347 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d186138, d187347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d186138, d187347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d186139 q = 0) : d187348 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d186139, d187348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d186139, d187348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d186140 q = 0) : d187349 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d186140, d187349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d186140, d187349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d186141 q = 0) : d187350 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d186141, d187350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d186141, d187350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d186142 q = 0) : d187351 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d186142, d187351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d186142, d187351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17093 (p : Pattern) (selected : d186148 p = 0) : d187357 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d186143 q = 0) : d187352 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d186143, d187352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17092 q selected
    | true =>
      simp only [d186143, d187352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d186144 q = 0) : d187353 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d186144, d187353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d186144, d187353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d186145 q = 0) : d187354 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d186145, d187354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d186145, d187354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d186146 q = 0) : d187355 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d186146, d187355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d186146, d187355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d186147 q = 0) : d187356 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d186147, d187356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d186147, d187356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d186148 q = 0) : d187357 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d186148, d187357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d186148, d187357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17094 (p : Pattern) (selected : d186154 p = 0) : d187363 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d186149 q = 0) : d187358 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d186149, d187358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17093 q selected
    | true =>
      simp only [d186149, d187358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d186150 q = 0) : d187359 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d186150, d187359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d186150, d187359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d186151 q = 0) : d187360 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d186151, d187360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d186151, d187360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d186152 q = 0) : d187361 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d186152, d187361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d186152, d187361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d186153 q = 0) : d187362 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d186153, d187362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d186153, d187362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d186154 q = 0) : d187363 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d186154, d187363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d186154, d187363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17095 (p : Pattern) (selected : d186160 p = 0) : d187369 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d186155 q = 0) : d187364 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d186155, d187364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17094 q selected
    | true =>
      simp only [d186155, d187364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d186156 q = 0) : d187365 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d186156, d187365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d186156, d187365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d186157 q = 0) : d187366 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d186157, d187366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d186157, d187366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d186158 q = 0) : d187367 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d186158, d187367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d186158, d187367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d186159 q = 0) : d187368 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d186159, d187368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d186159, d187368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d186160 q = 0) : d187369 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d186160, d187369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d186160, d187369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17096 (p : Pattern) (selected : d186166 p = 0) : d187375 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d186161 q = 0) : d187370 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d186161, d187370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17095 q selected
    | true =>
      simp only [d186161, d187370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d186162 q = 0) : d187371 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d186162, d187371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d186162, d187371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d186163 q = 0) : d187372 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d186163, d187372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d186163, d187372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d186164 q = 0) : d187373 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d186164, d187373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d186164, d187373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d186165 q = 0) : d187374 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d186165, d187374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d186165, d187374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d186166 q = 0) : d187375 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d186166, d187375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d186166, d187375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17097 (p : Pattern) (selected : d186172 p = 0) : d187381 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d186167 q = 0) : d187376 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d186167, d187376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17096 q selected
    | true =>
      simp only [d186167, d187376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d186168 q = 0) : d187377 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d186168, d187377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d186168, d187377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d186169 q = 0) : d187378 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d186169, d187378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d186169, d187378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d186170 q = 0) : d187379 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d186170, d187379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d186170, d187379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d186171 q = 0) : d187380 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d186171, d187380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d186171, d187380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d186172 q = 0) : d187381 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d186172, d187381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d186172, d187381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17098 (p : Pattern) (selected : d184787 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d170 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
    | true =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d171 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d172 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d184787 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d184787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro17099 (p : Pattern) (selected : d184793 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d184788 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d184788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17098 q selected
    | true =>
      simp only [d184788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184789 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d184789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184790 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d184790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d184791 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d184791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d184792 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d184792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d184792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d184793 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d184793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17100 (p : Pattern) (selected : d184799 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d184794 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17099 q selected
    | true =>
      simp only [d184794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184795 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184796 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d184796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184797 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d184797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d184798 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d184798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d184798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d184799 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d184799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17101 (p : Pattern) (selected : d184805 p = 1) : d187386 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d184766 q = 1) : d184766 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d184772 q = 1) : d184772 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d184786 q = 1) : d184786 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d184800 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17100 q selected
    | true =>
      simp only [d184800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d184801 q = 1) : d187382 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184801, d187382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184801, d187382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184694 q = 1) : d184694 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d184802 q = 1) : d187383 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184802, d187383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184802, d187383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d184803 q = 1) : d187384 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184803, d187384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184803, d187384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d184804 q = 1) : d187385 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d184804, d187385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d184804, d187385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d184805 q = 1) : d187386 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d184805, d187386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184805, d187386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro17102 (p : Pattern) (selected : d184817 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d184794 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17099 q selected
    | true =>
      simp only [d184794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184795 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184796 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d184796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184797 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d184797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d184798 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d184798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d184798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d184817 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d184817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17103 (p : Pattern) (selected : d184823 p = 1) : d187391 p = 1 := by
  have h0 (q : Pattern) (selected : d184766 q = 1) : d184766 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d184772 q = 1) : d184772 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d184786 q = 1) : d184786 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d184800 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17100 q selected
    | true =>
      simp only [d184800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d184801 q = 1) : d187382 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184801, d187382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184801, d187382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184694 q = 1) : d184694 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d184802 q = 1) : d187383 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184802, d187383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184802, d187383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d184803 q = 1) : d187384 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184803, d187384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d184803, d187384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d184804 q = 1) : d187385 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d184804, d187385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184804, d187385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d184810 q = 1) : d184810 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d184814 q = 1) : d184814 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d184816 q = 1) : d184816 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d184818 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17102 q selected
    | true =>
      simp only [d184818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h14 (q : Pattern) (selected : d184819 q = 1) : d187387 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184819, d187387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d184819, d187387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d184701 q = 1) : d184701 q = 1 := by
    exact selected
  have h16 (q : Pattern) (selected : d184820 q = 1) : d187388 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184820, d187388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d184820, d187388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d184821 q = 1) : d187389 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184821, d187389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d184821, d187389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d184822 q = 1) : d187390 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d184822, d187390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d184822, d187390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d184823 q = 1) : d187391 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d184823, d187391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d184823, d187391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro17104 (p : Pattern) (selected : d184832 p = 1) : d187398 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d184816 q = 1) : d184816 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d184818 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17102 q selected
    | true =>
      simp only [d184818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d184819 q = 1) : d187387 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184819, d187387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d184819, d187387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d184701 q = 1) : d184701 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d184820 q = 1) : d187388 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184820, d187388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184820, d187388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184830 q = 1) : d187396 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184830, d187396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184830, d187396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d184831 q = 1) : d187397 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d184831, d187397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184831, d187397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d184832 q = 1) : d187398 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d184832, d187398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184832, d187398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro17105 (p : Pattern) (selected : d184852 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d245 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
  have h2 (q : Pattern) (selected : d170 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
    | true =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d171 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184852 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d184852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17106 (p : Pattern) (selected : d184858 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d184853 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d184853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17105 q selected
    | true =>
      simp only [d184853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184854 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d184854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184855 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d184855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d184856 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d184856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d184857 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d184857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d184857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d184858 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d184858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17107 (p : Pattern) (selected : d184864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d184859 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17106 q selected
    | true =>
      simp only [d184859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184860 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184861 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d184861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184862 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d184862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d184863 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d184863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d184863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d184864 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d184864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17108 (p : Pattern) (selected : d184870 p = 1) : d187408 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d184851 q = 1) : d184851 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d184865 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17107 q selected
    | true =>
      simp only [d184865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d184866 q = 1) : d187404 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184866, d187404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d184866, d187404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d184730 q = 1) : d184730 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d184867 q = 1) : d187405 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184867, d187405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184867, d187405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184868 q = 1) : d187406 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184868, d187406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184868, d187406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d184869 q = 1) : d187407 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d184869, d187407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184869, d187407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d184870 q = 1) : d187408 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d184870, d187408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184870, d187408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro17109 (p : Pattern) (selected : d184876 p = 1) : d187414 p = 1 := by
  have h0 (q : Pattern) (selected : d184760 q = 1) : d184760 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d184824 q = 1) : d187392 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d184824, d187392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17101 q selected
    | true =>
      simp only [d184824, d187392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17103 q selected
  have h2 (q : Pattern) (selected : d184826 q = 1) : d184826 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d184827 q = 1) : d187393 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d184827, d187393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d184827, d187393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d184828 q = 1) : d187394 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d184828, d187394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184828, d187394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184829 q = 1) : d187395 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d184829, d187395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184829, d187395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d184833 q = 1) : d187399 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d184833, d187399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d184833, d187399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17104 q selected
  have h8 (q : Pattern) (selected : d184834 q = 1) : d187400 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d184834, d187400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d184834, d187400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d184835 q = 1) : d187401 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d184835, d187401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d184835, d187401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d184836 q = 1) : d187402 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d184836, d187402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d184836, d187402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d184837 q = 1) : d187403 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d184837, d187403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d184837, d187403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d184871 q = 1) : d187409 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d184871, d187409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d184871, d187409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17108 q selected
  have h13 (q : Pattern) (selected : d184872 q = 1) : d187410 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d184872, d187410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d184872, d187410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d184873 q = 1) : d187411 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d184873, d187411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d184873, d187411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d184874 q = 1) : d187412 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d184874, d187412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d184874, d187412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d184875 q = 1) : d187413 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d184875, d187413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d184875, d187413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d184876 q = 1) : d187414 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d184876, d187414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d184876, d187414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro17110 (p : Pattern) (selected : d184882 p = 1) : d187420 p = 1 := by
  have h0 (q : Pattern) (selected : d184745 q = 1) : d184745 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d184877 q = 1) : d187415 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d184877, d187415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d184877, d187415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17109 q selected
  have h3 (q : Pattern) (selected : d184878 q = 1) : d187416 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d184878, d187416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d184878, d187416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d184879 q = 1) : d187417 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d184879, d187417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d184879, d187417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d184880 q = 1) : d187418 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d184880, d187418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d184880, d187418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184881 q = 1) : d187419 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d184881, d187419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d184881, d187419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d184882 q = 1) : d187420 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d184882, d187420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184882, d187420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro17111 (p : Pattern) (selected : d184924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d350 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15 q selected
    | true =>
      simp only [d350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d351 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d170 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
    | true =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d171 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d172 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d184924 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d184924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro17112 (p : Pattern) (selected : d184930 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d184925 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d184925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17111 q selected
    | true =>
      simp only [d184925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17098 q selected
  have h2 (q : Pattern) (selected : d184926 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d184926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184927 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d184927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d184788 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d184788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17098 q selected
    | true =>
      simp only [d184788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d184789 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d184789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184790 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d184790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d184928 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d184928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d184791 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d184791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d184791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d184929 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d184929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d184929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d184930 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d184930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d184930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro17113 (p : Pattern) (selected : d184936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d184931 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17112 q selected
    | true =>
      simp only [d184931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184932 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184794 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17099 q selected
    | true =>
      simp only [d184794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184795 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d184933 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d184933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184934 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d184934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d184935 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d184935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d184935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d184936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d184936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro17114 (p : Pattern) (selected : d184948 p = 1) : d187425 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d184903 q = 1) : d184903 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d184909 q = 1) : d184909 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d184923 q = 1) : d184923 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d184937 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17113 q selected
    | true =>
      simp only [d184937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17100 q selected
  have h5 (q : Pattern) (selected : d184938 q = 1) : d187421 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184938, d187421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184938, d187421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184944 q = 1) : d184944 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d184945 q = 1) : d187422 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184945, d187422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184945, d187422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d184946 q = 1) : d187423 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184946, d187423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184946, d187423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d184947 q = 1) : d187424 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d184947, d187424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d184947, d187424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d184948 q = 1) : d187425 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d184948, d187425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184948, d187425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro17115 (p : Pattern) (selected : d184960 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d184931 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17112 q selected
    | true =>
      simp only [d184931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d184932 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184794 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17099 q selected
    | true =>
      simp only [d184794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184795 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d184933 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d184933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184934 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d184934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d184934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d184935 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d184935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d184935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d184960 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d184960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d184960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17116 (p : Pattern) (selected : d184969 p = 1) : d187430 p = 1 := by
  have h0 (q : Pattern) (selected : d184903 q = 1) : d184903 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d184909 q = 1) : d184909 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d184923 q = 1) : d184923 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d184937 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17113 q selected
    | true =>
      simp only [d184937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17100 q selected
  have h4 (q : Pattern) (selected : d184938 q = 1) : d187421 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184938, d187421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184938, d187421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d184944 q = 1) : d184944 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d184945 q = 1) : d187422 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184945, d187422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d184945, d187422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d184946 q = 1) : d187423 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184946, d187423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d184946, d187423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d184947 q = 1) : d187424 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d184947, d187424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184947, d187424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d184953 q = 1) : d184953 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d184957 q = 1) : d184957 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d184959 q = 1) : d184959 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d184961 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17115 q selected
    | true =>
      simp only [d184961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17102 q selected
  have h13 (q : Pattern) (selected : d184962 q = 1) : d187426 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184962, d187426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d184962, d187426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d184965 q = 1) : d184965 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d184966 q = 1) : d187427 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184966, d187427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d184966, d187427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d184967 q = 1) : d187428 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184967, d187428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d184967, d187428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d184968 q = 1) : d187429 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d184968, d187429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d184968, d187429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d184969 q = 1) : d187430 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d184969, d187430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d184969, d187430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro17117 (p : Pattern) (selected : d184978 p = 1) : d187437 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d184959 q = 1) : d184959 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d184961 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d184961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17115 q selected
    | true =>
      simp only [d184961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17102 q selected
  have h3 (q : Pattern) (selected : d184962 q = 1) : d187426 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d184962, d187426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d184962, d187426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d184965 q = 1) : d184965 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d184966 q = 1) : d187427 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d184966, d187427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184966, d187427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184976 q = 1) : d187435 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d184976, d187435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184976, d187435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d184977 q = 1) : d187436 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d184977, d187436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184977, d187436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d184978 q = 1) : d187437 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d184978, d187437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184978, d187437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro17118 (p : Pattern) (selected : d185000 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d431 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15 q selected
  have h2 (q : Pattern) (selected : d350 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15 q selected
    | true =>
      simp only [d350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d432 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d351 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d433 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d245 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
  have h7 (q : Pattern) (selected : d170 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
    | true =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d246 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d171 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d247 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185000 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro17119 (p : Pattern) (selected : d185006 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185001 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17118 q selected
    | true =>
      simp only [d185001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17105 q selected
  have h2 (q : Pattern) (selected : d185002 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185003 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d184853 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d184853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17105 q selected
    | true =>
      simp only [d184853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d184854 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d184854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184855 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d184855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185004 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d184856 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d184856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d184856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d185005 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185006 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d185006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro17120 (p : Pattern) (selected : d185012 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185007 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17119 q selected
    | true =>
      simp only [d185007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185008 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184859 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d184859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17106 q selected
    | true =>
      simp only [d184859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d184860 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d184860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185009 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185010 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185011 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185012 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17121 (p : Pattern) (selected : d185024 p = 1) : d187447 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d184999 q = 1) : d184999 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d185013 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17120 q selected
    | true =>
      simp only [d185013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17107 q selected
  have h3 (q : Pattern) (selected : d185014 q = 1) : d187443 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185014, d187443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185014, d187443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185020 q = 1) : d185020 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d185021 q = 1) : d187444 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185021, d187444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185021, d187444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185022 q = 1) : d187445 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185022, d187445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185022, d187445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185023 q = 1) : d187446 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185023, d187446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185023, d187446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185024 q = 1) : d187447 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185024, d187447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185024, d187447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro17122 (p : Pattern) (selected : d185036 p = 1) : d187453 p = 1 := by
  have h0 (q : Pattern) (selected : d184897 q = 1) : d184897 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d184970 q = 1) : d187431 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d184970, d187431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17114 q selected
    | true =>
      simp only [d184970, d187431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17116 q selected
  have h2 (q : Pattern) (selected : d184972 q = 1) : d184972 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d184973 q = 1) : d187432 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d184973, d187432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d184973, d187432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d184974 q = 1) : d187433 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d184974, d187433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d184974, d187433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d184975 q = 1) : d187434 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d184975, d187434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d184975, d187434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d184979 q = 1) : d187438 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d184979, d187438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d184979, d187438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17117 q selected
  have h8 (q : Pattern) (selected : d184981 q = 1) : d184981 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d184982 q = 1) : d187439 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d184982, d187439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d184982, d187439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d184983 q = 1) : d187440 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d184983, d187440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d184983, d187440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d184984 q = 1) : d187441 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d184984, d187441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d184984, d187441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d184985 q = 1) : d187442 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d184985, d187442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d184985, d187442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d185025 q = 1) : d187448 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d185025, d187448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185025, d187448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17121 q selected
  have h14 (q : Pattern) (selected : d185031 q = 1) : d185031 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d185032 q = 1) : d187449 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d185032, d187449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d185032, d187449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d185033 q = 1) : d187450 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d185033, d187450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d185033, d187450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d185034 q = 1) : d187451 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d185034, d187451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d185034, d187451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d185035 q = 1) : d187452 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d185035, d187452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d185035, d187452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d185036 q = 1) : d187453 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d185036, d187453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d185036, d187453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro17123 (p : Pattern) (selected : d185042 p = 1) : d187459 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185037 q = 1) : d187454 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d185037, d187454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185037, d187454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17122 q selected
  have h2 (q : Pattern) (selected : d185038 q = 1) : d187455 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d185038, d187455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185038, d187455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185039 q = 1) : d187456 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d185039, d187456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185039, d187456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185040 q = 1) : d187457 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d185040, d187457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185040, d187457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185041 q = 1) : d187458 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d185041, d187458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185041, d187458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185042 q = 1) : d187459 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d185042, d187459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185042, d187459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17124 (p : Pattern) (selected : d185120 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d9661 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6823 q selected
    | true =>
      simp only [d9661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9663 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d16292 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d874 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro52 q selected
    | true =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d875 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d876 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185120 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro17125 (p : Pattern) (selected : d185121 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d874 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro52 q selected
    | true =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d875 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d876 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185121 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro17126 (p : Pattern) (selected : d185131 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185122 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17124 q selected
    | true =>
      simp only [d185122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17125 q selected
  have h2 (q : Pattern) (selected : d185123 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185124 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185125 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17125 q selected
    | true =>
      simp only [d185125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185126 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185127 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185128 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185129 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d185130 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185131 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d185131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro17127 (p : Pattern) (selected : d185135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185125 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17125 q selected
    | true =>
      simp only [d185125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185126 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185127 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185129 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185134 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185135 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17128 (p : Pattern) (selected : d185141 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185132 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17126 q selected
    | true =>
      simp only [d185132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185133 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185136 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17127 q selected
    | true =>
      simp only [d185136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185137 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185138 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185139 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185140 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185141 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro17129 (p : Pattern) (selected : d185145 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185136 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17127 q selected
    | true =>
      simp only [d185136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185137 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185142 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185143 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185144 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185145 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17130 (p : Pattern) (selected : d185157 p = 1) : d187465 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185096 q = 1) : d185096 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d185105 q = 1) : d185105 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d185119 q = 1) : d185119 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d185146 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17128 q selected
    | true =>
      simp only [d185146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17129 q selected
  have h5 (q : Pattern) (selected : d185147 q = 1) : d187461 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185147, d187461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185147, d187461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185153 q = 1) : d185153 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d185154 q = 1) : d187462 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185154, d187462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185154, d187462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185155 q = 1) : d187463 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185155, d187463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185155, d187463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d185156 q = 1) : d187464 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185156, d187464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185156, d187464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185157 q = 1) : d187465 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185157, d187465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185157, d187465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro17131 (p : Pattern) (selected : d185171 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185132 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17126 q selected
    | true =>
      simp only [d185132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185133 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185136 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17127 q selected
    | true =>
      simp only [d185136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185137 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185138 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185139 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185140 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185171 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17132 (p : Pattern) (selected : d185172 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185136 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17127 q selected
    | true =>
      simp only [d185136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185137 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185142 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185143 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185144 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185172 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17133 (p : Pattern) (selected : d185181 p = 1) : d187470 p = 1 := by
  have h0 (q : Pattern) (selected : d185096 q = 1) : d185096 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185105 q = 1) : d185105 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d185119 q = 1) : d185119 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d185146 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17128 q selected
    | true =>
      simp only [d185146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17129 q selected
  have h4 (q : Pattern) (selected : d185147 q = 1) : d187461 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185147, d187461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185147, d187461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185153 q = 1) : d185153 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d185154 q = 1) : d187462 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185154, d187462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185154, d187462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185155 q = 1) : d187463 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185155, d187463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185155, d187463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185156 q = 1) : d187464 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185156, d187464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185156, d187464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d185163 q = 1) : d185163 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d185168 q = 1) : d185168 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d185170 q = 1) : d185170 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d185173 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17131 q selected
    | true =>
      simp only [d185173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17132 q selected
  have h13 (q : Pattern) (selected : d185174 q = 1) : d187466 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185174, d187466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d185174, d187466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d185177 q = 1) : d185177 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d185178 q = 1) : d187467 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185178, d187467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d185178, d187467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d185179 q = 1) : d187468 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185179, d187468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d185179, d187468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d185180 q = 1) : d187469 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185180, d187469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d185180, d187469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d185181 q = 1) : d187470 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185181, d187470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d185181, d187470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro17134 (p : Pattern) (selected : d185201 p = 1) : d187477 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185170 q = 1) : d185170 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d185173 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17131 q selected
    | true =>
      simp only [d185173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17132 q selected
  have h3 (q : Pattern) (selected : d185174 q = 1) : d187466 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185174, d187466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185174, d187466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185177 q = 1) : d185177 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d185178 q = 1) : d187467 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185178, d187467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185178, d187467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185199 q = 1) : d187475 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185199, d187475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185199, d187475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185200 q = 1) : d187476 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185200, d187476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185200, d187476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185201 q = 1) : d187477 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185201, d187477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185201, d187477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro17135 (p : Pattern) (selected : d185245 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d16393 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6823 q selected
  have h2 (q : Pattern) (selected : d9661 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6823 q selected
    | true =>
      simp only [d9661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d16394 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d16394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9663 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d16395 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d16395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1018 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro52 q selected
  have h7 (q : Pattern) (selected : d874 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro52 q selected
    | true =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d1019 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d875 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d1020 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185245 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro17136 (p : Pattern) (selected : d185246 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1018 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro52 q selected
  have h2 (q : Pattern) (selected : d874 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro52 q selected
    | true =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1019 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d875 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1020 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185246 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17137 (p : Pattern) (selected : d185256 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185247 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17135 q selected
    | true =>
      simp only [d185247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17136 q selected
  have h2 (q : Pattern) (selected : d185248 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185249 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185250 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17136 q selected
    | true =>
      simp only [d185250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185251 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185252 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185253 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185254 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d185255 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185256 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d185256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro17138 (p : Pattern) (selected : d185260 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185250 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17136 q selected
    | true =>
      simp only [d185250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185251 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185252 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185254 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185259 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185260 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17139 (p : Pattern) (selected : d185266 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185257 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17137 q selected
    | true =>
      simp only [d185257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185258 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185261 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17138 q selected
    | true =>
      simp only [d185261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185262 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185263 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185264 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185265 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185266 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17140 (p : Pattern) (selected : d185270 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185261 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17138 q selected
    | true =>
      simp only [d185261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185262 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185267 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185268 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185269 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185270 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17141 (p : Pattern) (selected : d185282 p = 1) : d187487 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185244 q = 1) : d185244 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d185271 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17139 q selected
    | true =>
      simp only [d185271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17140 q selected
  have h3 (q : Pattern) (selected : d185272 q = 1) : d187483 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185272, d187483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185272, d187483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185278 q = 1) : d185278 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d185279 q = 1) : d187484 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185279, d187484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185279, d187484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185280 q = 1) : d187485 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185280, d187485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185280, d187485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185281 q = 1) : d187486 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185281, d187486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185281, d187486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185282 q = 1) : d187487 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185282, d187487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185282, d187487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro17142 (p : Pattern) (selected : d185299 p = 1) : d187493 p = 1 := by
  have h0 (q : Pattern) (selected : d185088 q = 1) : d185088 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185182 q = 1) : d187471 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d185182, d187471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17130 q selected
    | true =>
      simp only [d185182, d187471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17133 q selected
  have h2 (q : Pattern) (selected : d185195 q = 1) : d185195 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d185196 q = 1) : d187472 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d185196, d187472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185196, d187472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d185197 q = 1) : d187473 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d185197, d187473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185197, d187473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185198 q = 1) : d187474 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d185198, d187474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185198, d187474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185202 q = 1) : d187478 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d185202, d187478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185202, d187478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17134 q selected
  have h8 (q : Pattern) (selected : d185204 q = 1) : d185204 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d185205 q = 1) : d187479 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d185205, d187479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185205, d187479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185206 q = 1) : d187480 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d185206, d187480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d185206, d187480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d185207 q = 1) : d187481 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d185207, d187481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d185207, d187481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d185208 q = 1) : d187482 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d185208, d187482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185208, d187482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d185283 q = 1) : d187488 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d185283, d187488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185283, d187488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17141 q selected
  have h14 (q : Pattern) (selected : d185294 q = 1) : d185294 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d185295 q = 1) : d187489 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d185295, d187489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d185295, d187489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d185296 q = 1) : d187490 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d185296, d187490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d185296, d187490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d185297 q = 1) : d187491 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d185297, d187491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d185297, d187491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d185298 q = 1) : d187492 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d185298, d187492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d185298, d187492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d185299 q = 1) : d187493 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d185299, d187493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d185299, d187493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro17143 (p : Pattern) (selected : d185305 p = 1) : d187499 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185300 q = 1) : d187494 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d185300, d187494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185300, d187494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17142 q selected
  have h2 (q : Pattern) (selected : d185301 q = 1) : d187495 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d185301, d187495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185301, d187495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185302 q = 1) : d187496 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d185302, d187496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185302, d187496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185303 q = 1) : d187497 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d185303, d187497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185303, d187497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185304 q = 1) : d187498 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d185304, d187498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185304, d187498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185305 q = 1) : d187499 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d185305, d187499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185305, d187499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17144 (p : Pattern) (selected : d185388 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d9896 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6837 q selected
    | true =>
      simp only [d9896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9898 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d16539 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9918 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6839 q selected
    | true =>
      simp only [d9918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d9920 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d14873 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185388 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro17145 (p : Pattern) (selected : d185389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1276 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro81 q selected
    | true =>
      simp only [d1276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1277 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1278 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185389 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro17146 (p : Pattern) (selected : d185399 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185390 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17144 q selected
    | true =>
      simp only [d185390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17145 q selected
  have h2 (q : Pattern) (selected : d185391 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185392 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185393 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17145 q selected
    | true =>
      simp only [d185393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185394 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185395 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185396 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185397 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d185398 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185399 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d185399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro17147 (p : Pattern) (selected : d185403 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185393 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17145 q selected
    | true =>
      simp only [d185393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185394 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185395 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185397 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185402 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185403 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17148 (p : Pattern) (selected : d185409 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185400 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17146 q selected
    | true =>
      simp only [d185400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185401 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185404 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17147 q selected
    | true =>
      simp only [d185404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185405 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185406 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185407 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185408 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185409 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro17149 (p : Pattern) (selected : d185413 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185404 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17147 q selected
    | true =>
      simp only [d185404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185405 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185410 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185411 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185412 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185413 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17150 (p : Pattern) (selected : d185425 p = 1) : d187506 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185360 q = 1) : d185360 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d185369 q = 1) : d185369 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d185387 q = 1) : d185387 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d185414 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17148 q selected
    | true =>
      simp only [d185414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17149 q selected
  have h5 (q : Pattern) (selected : d185415 q = 1) : d187502 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185415, d187502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185415, d187502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185421 q = 1) : d185421 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d185422 q = 1) : d187503 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185422, d187503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185422, d187503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185423 q = 1) : d187504 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185423, d187504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185423, d187504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d185424 q = 1) : d187505 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185424, d187505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185424, d187505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185425 q = 1) : d187506 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185425, d187506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185425, d187506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro17151 (p : Pattern) (selected : d185439 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185400 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17146 q selected
    | true =>
      simp only [d185400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185401 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185404 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17147 q selected
    | true =>
      simp only [d185404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185405 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185406 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185407 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185408 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185439 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17152 (p : Pattern) (selected : d185440 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185404 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17147 q selected
    | true =>
      simp only [d185404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185405 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185410 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185411 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185412 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185440 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17153 (p : Pattern) (selected : d185449 p = 1) : d187511 p = 1 := by
  have h0 (q : Pattern) (selected : d185360 q = 1) : d185360 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185369 q = 1) : d185369 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d185387 q = 1) : d185387 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d185414 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17148 q selected
    | true =>
      simp only [d185414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17149 q selected
  have h4 (q : Pattern) (selected : d185415 q = 1) : d187502 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185415, d187502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185415, d187502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185421 q = 1) : d185421 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d185422 q = 1) : d187503 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185422, d187503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185422, d187503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185423 q = 1) : d187504 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185423, d187504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185423, d187504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185424 q = 1) : d187505 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185424, d187505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185424, d187505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d185431 q = 1) : d185431 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d185436 q = 1) : d185436 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d185438 q = 1) : d185438 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d185441 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17151 q selected
    | true =>
      simp only [d185441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17152 q selected
  have h13 (q : Pattern) (selected : d185442 q = 1) : d187507 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185442, d187507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d185442, d187507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d185445 q = 1) : d185445 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d185446 q = 1) : d187508 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185446, d187508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d185446, d187508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d185447 q = 1) : d187509 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185447, d187509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d185447, d187509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d185448 q = 1) : d187510 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185448, d187510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d185448, d187510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d185449 q = 1) : d187511 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185449, d187511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d185449, d187511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro17154 (p : Pattern) (selected : d185469 p = 1) : d187518 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185438 q = 1) : d185438 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d185441 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17151 q selected
    | true =>
      simp only [d185441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17152 q selected
  have h3 (q : Pattern) (selected : d185442 q = 1) : d187507 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185442, d187507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185442, d187507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185445 q = 1) : d185445 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d185446 q = 1) : d187508 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185446, d187508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185446, d187508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185467 q = 1) : d187516 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185467, d187516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185467, d187516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185468 q = 1) : d187517 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185468, d187517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185468, d187517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185469 q = 1) : d187518 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185469, d187518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185469, d187518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro17155 (p : Pattern) (selected : d185517 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d16706 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6837 q selected
  have h2 (q : Pattern) (selected : d9896 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6837 q selected
    | true =>
      simp only [d9896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d16707 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d16707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9898 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d16708 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d16708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15064 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6839 q selected
  have h7 (q : Pattern) (selected : d9918 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6839 q selected
    | true =>
      simp only [d9918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15065 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d9920 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d9920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15066 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185517 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro17156 (p : Pattern) (selected : d185518 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1447 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro81 q selected
  have h2 (q : Pattern) (selected : d1276 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro81 q selected
    | true =>
      simp only [d1276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1448 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1277 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1449 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185518 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17157 (p : Pattern) (selected : d185528 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185519 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17155 q selected
    | true =>
      simp only [d185519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17156 q selected
  have h2 (q : Pattern) (selected : d185520 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185521 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185522 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17156 q selected
    | true =>
      simp only [d185522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185523 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185524 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185525 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185526 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d185527 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185528 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d185528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro17158 (p : Pattern) (selected : d185532 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185522 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17156 q selected
    | true =>
      simp only [d185522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185523 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185524 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185526 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185531 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185532 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17159 (p : Pattern) (selected : d185538 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185529 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17157 q selected
    | true =>
      simp only [d185529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185530 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185533 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17158 q selected
    | true =>
      simp only [d185533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185534 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185535 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185536 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185537 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185538 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17160 (p : Pattern) (selected : d185542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185533 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17158 q selected
    | true =>
      simp only [d185533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185534 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185539 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185540 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185541 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185542 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17161 (p : Pattern) (selected : d185554 p = 1) : d187528 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185516 q = 1) : d185516 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d185543 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17159 q selected
    | true =>
      simp only [d185543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17160 q selected
  have h3 (q : Pattern) (selected : d185544 q = 1) : d187524 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185544, d187524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185544, d187524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185550 q = 1) : d185550 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d185551 q = 1) : d187525 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185551, d187525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185551, d187525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185552 q = 1) : d187526 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185552, d187526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185552, d187526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185553 q = 1) : d187527 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185553, d187527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185553, d187527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185554 q = 1) : d187528 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185554, d187528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185554, d187528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro17162 (p : Pattern) (selected : d185571 p = 1) : d187534 p = 1 := by
  have h0 (q : Pattern) (selected : d185352 q = 1) : d185352 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185450 q = 1) : d187512 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d185450, d187512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17150 q selected
    | true =>
      simp only [d185450, d187512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17153 q selected
  have h2 (q : Pattern) (selected : d185463 q = 1) : d185463 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d185464 q = 1) : d187513 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d185464, d187513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185464, d187513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d185465 q = 1) : d187514 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d185465, d187514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185465, d187514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185466 q = 1) : d187515 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d185466, d187515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185466, d187515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185470 q = 1) : d187519 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d185470, d187519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185470, d187519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17154 q selected
  have h8 (q : Pattern) (selected : d185472 q = 1) : d185472 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d185473 q = 1) : d187520 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d185473, d187520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185473, d187520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185474 q = 1) : d187521 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d185474, d187521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d185474, d187521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d185475 q = 1) : d187522 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d185475, d187522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d185475, d187522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d185476 q = 1) : d187523 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d185476, d187523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185476, d187523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d185555 q = 1) : d187529 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d185555, d187529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185555, d187529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17161 q selected
  have h14 (q : Pattern) (selected : d185566 q = 1) : d185566 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d185567 q = 1) : d187530 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d185567, d187530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d185567, d187530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d185568 q = 1) : d187531 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d185568, d187531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d185568, d187531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d185569 q = 1) : d187532 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d185569, d187532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d185569, d187532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d185570 q = 1) : d187533 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d185570, d187533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d185570, d187533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d185571 q = 1) : d187534 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d185571, d187534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d185571, d187534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro17163 (p : Pattern) (selected : d185577 p = 1) : d187540 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185572 q = 1) : d187535 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d185572, d187535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185572, d187535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17162 q selected
  have h2 (q : Pattern) (selected : d185573 q = 1) : d187536 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d185573, d187536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185573, d187536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185574 q = 1) : d187537 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d185574, d187537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185574, d187537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185575 q = 1) : d187538 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d185575, d187538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185575, d187538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185576 q = 1) : d187539 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d185576, d187539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185576, d187539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185577 q = 1) : d187540 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d185577, d187540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185577, d187540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17164 (p : Pattern) (selected : d185661 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10190 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6855 q selected
    | true =>
      simp only [d10190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10192 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d16891 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10215 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6857 q selected
    | true =>
      simp only [d10215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10217 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15266 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185661 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro17165 (p : Pattern) (selected : d185662 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10226 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6859 q selected
    | true =>
      simp only [d10226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10228 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d16896 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185662 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro17166 (p : Pattern) (selected : d185672 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185663 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17164 q selected
    | true =>
      simp only [d185663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17165 q selected
  have h2 (q : Pattern) (selected : d185664 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185665 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185666 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17165 q selected
    | true =>
      simp only [d185666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185667 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185668 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185669 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185670 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d185671 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185672 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d185672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro17167 (p : Pattern) (selected : d185676 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185666 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17165 q selected
    | true =>
      simp only [d185666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185667 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185668 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185670 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185675 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185676 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17168 (p : Pattern) (selected : d185682 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185673 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17166 q selected
    | true =>
      simp only [d185673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185674 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185677 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17167 q selected
    | true =>
      simp only [d185677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185678 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185679 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185680 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185681 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185682 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro17169 (p : Pattern) (selected : d185686 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185677 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17167 q selected
    | true =>
      simp only [d185677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185678 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185683 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185685 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185686 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17170 (p : Pattern) (selected : d185698 p = 1) : d187548 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185633 q = 1) : d185633 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d185642 q = 1) : d185642 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d185660 q = 1) : d185660 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d185687 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17168 q selected
    | true =>
      simp only [d185687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17169 q selected
  have h5 (q : Pattern) (selected : d185688 q = 1) : d187544 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185688, d187544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185688, d187544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185694 q = 1) : d185694 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d185695 q = 1) : d187545 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185695, d187545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185695, d187545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185696 q = 1) : d187546 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185696, d187546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185696, d187546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d185697 q = 1) : d187547 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185697, d187547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185697, d187547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185698 q = 1) : d187548 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185698, d187548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185698, d187548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro17171 (p : Pattern) (selected : d185712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185673 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17166 q selected
    | true =>
      simp only [d185673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185674 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185677 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17167 q selected
    | true =>
      simp only [d185677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185678 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185679 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185680 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185681 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185712 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17172 (p : Pattern) (selected : d185713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185677 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17167 q selected
    | true =>
      simp only [d185677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185678 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185683 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185684 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185685 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185713 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17173 (p : Pattern) (selected : d185722 p = 1) : d187553 p = 1 := by
  have h0 (q : Pattern) (selected : d185633 q = 1) : d185633 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185642 q = 1) : d185642 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d185660 q = 1) : d185660 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d185687 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17168 q selected
    | true =>
      simp only [d185687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17169 q selected
  have h4 (q : Pattern) (selected : d185688 q = 1) : d187544 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185688, d187544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185688, d187544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185694 q = 1) : d185694 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d185695 q = 1) : d187545 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185695, d187545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185695, d187545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185696 q = 1) : d187546 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185696, d187546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185696, d187546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185697 q = 1) : d187547 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185697, d187547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185697, d187547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d185704 q = 1) : d185704 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d185709 q = 1) : d185709 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d185711 q = 1) : d185711 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d185714 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17171 q selected
    | true =>
      simp only [d185714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17172 q selected
  have h13 (q : Pattern) (selected : d185715 q = 1) : d187549 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185715, d187549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d185715, d187549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d185718 q = 1) : d185718 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d185719 q = 1) : d187550 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185719, d187550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d185719, d187550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d185720 q = 1) : d187551 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185720, d187551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d185720, d187551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d185721 q = 1) : d187552 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185721, d187552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d185721, d187552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d185722 q = 1) : d187553 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185722, d187553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d185722, d187553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro17174 (p : Pattern) (selected : d185742 p = 1) : d187560 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185711 q = 1) : d185711 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d185714 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17171 q selected
    | true =>
      simp only [d185714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17172 q selected
  have h3 (q : Pattern) (selected : d185715 q = 1) : d187549 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185715, d187549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185715, d187549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185718 q = 1) : d185718 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d185719 q = 1) : d187550 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185719, d187550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185719, d187550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185740 q = 1) : d187558 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185740, d187558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185740, d187558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185741 q = 1) : d187559 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185741, d187559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185741, d187559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185742 q = 1) : d187560 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185742, d187560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185742, d187560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro17175 (p : Pattern) (selected : d185790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d17066 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6855 q selected
  have h2 (q : Pattern) (selected : d10190 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6855 q selected
    | true =>
      simp only [d10190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d17067 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d17067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10192 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17068 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15457 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6857 q selected
  have h7 (q : Pattern) (selected : d10215 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6857 q selected
    | true =>
      simp only [d10215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15458 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10217 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15459 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d185790 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro17176 (p : Pattern) (selected : d185791 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d17073 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6859 q selected
  have h2 (q : Pattern) (selected : d10226 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6859 q selected
    | true =>
      simp only [d10226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d17074 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d17074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10228 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17075 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185791 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17177 (p : Pattern) (selected : d185801 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185792 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17175 q selected
    | true =>
      simp only [d185792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17176 q selected
  have h2 (q : Pattern) (selected : d185793 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185794 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185795 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17176 q selected
    | true =>
      simp only [d185795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185796 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185797 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185798 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185799 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d185800 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185801 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d185801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro17178 (p : Pattern) (selected : d185805 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185795 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17176 q selected
    | true =>
      simp only [d185795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185796 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185797 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185799 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185804 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185805 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17179 (p : Pattern) (selected : d185811 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185802 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17177 q selected
    | true =>
      simp only [d185802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185803 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185806 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17178 q selected
    | true =>
      simp only [d185806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185807 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185808 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185809 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185810 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185811 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17180 (p : Pattern) (selected : d185815 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185806 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17178 q selected
    | true =>
      simp only [d185806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185807 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185812 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185813 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185814 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185815 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17181 (p : Pattern) (selected : d185827 p = 1) : d187570 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185789 q = 1) : d185789 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d185816 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17179 q selected
    | true =>
      simp only [d185816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17180 q selected
  have h3 (q : Pattern) (selected : d185817 q = 1) : d187566 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185817, d187566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185817, d187566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185823 q = 1) : d185823 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d185824 q = 1) : d187567 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185824, d187567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185824, d187567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185825 q = 1) : d187568 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185825, d187568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185825, d187568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185826 q = 1) : d187569 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185826, d187569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185826, d187569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185827 q = 1) : d187570 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185827, d187570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185827, d187570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro17182 (p : Pattern) (selected : d185844 p = 1) : d187576 p = 1 := by
  have h0 (q : Pattern) (selected : d185625 q = 1) : d185625 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185723 q = 1) : d187554 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d185723, d187554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17170 q selected
    | true =>
      simp only [d185723, d187554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17173 q selected
  have h2 (q : Pattern) (selected : d185736 q = 1) : d185736 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d185737 q = 1) : d187555 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d185737, d187555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185737, d187555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d185738 q = 1) : d187556 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d185738, d187556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185738, d187556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185739 q = 1) : d187557 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d185739, d187557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185739, d187557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185743 q = 1) : d187561 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d185743, d187561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185743, d187561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17174 q selected
  have h8 (q : Pattern) (selected : d185745 q = 1) : d185745 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d185746 q = 1) : d187562 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d185746, d187562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185746, d187562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185747 q = 1) : d187563 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d185747, d187563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d185747, d187563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d185748 q = 1) : d187564 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d185748, d187564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d185748, d187564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d185749 q = 1) : d187565 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d185749, d187565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185749, d187565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d185828 q = 1) : d187571 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d185828, d187571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185828, d187571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17181 q selected
  have h14 (q : Pattern) (selected : d185839 q = 1) : d185839 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d185840 q = 1) : d187572 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d185840, d187572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d185840, d187572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d185841 q = 1) : d187573 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d185841, d187573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d185841, d187573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d185842 q = 1) : d187574 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d185842, d187574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d185842, d187574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d185843 q = 1) : d187575 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d185843, d187575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d185843, d187575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d185844 q = 1) : d187576 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d185844, d187576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d185844, d187576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro17183 (p : Pattern) (selected : d185850 p = 1) : d187582 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185845 q = 1) : d187577 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d185845, d187577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185845, d187577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17182 q selected
  have h2 (q : Pattern) (selected : d185846 q = 1) : d187578 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d185846, d187578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185846, d187578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185847 q = 1) : d187579 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d185847, d187579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185847, d187579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185848 q = 1) : d187580 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d185848, d187580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185848, d187580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185849 q = 1) : d187581 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d185849, d187581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185849, d187581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185850 q = 1) : d187582 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d185850, d187582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185850, d187582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17184 (p : Pattern) (selected : d185935 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10458 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6872 q selected
    | true =>
      simp only [d10458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10460 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d17256 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10482 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6874 q selected
    | true =>
      simp only [d10482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10484 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15654 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185935 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro17185 (p : Pattern) (selected : d185936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10493 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6876 q selected
    | true =>
      simp only [d10493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10495 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d17261 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185936 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d185936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro17186 (p : Pattern) (selected : d185946 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185937 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17184 q selected
    | true =>
      simp only [d185937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17185 q selected
  have h2 (q : Pattern) (selected : d185938 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185939 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185940 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17185 q selected
    | true =>
      simp only [d185940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185941 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185942 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185943 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185944 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d185945 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185946 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d185946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro17187 (p : Pattern) (selected : d185950 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185940 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d185940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17185 q selected
    | true =>
      simp only [d185940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185941 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d185941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185942 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d185942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185944 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d185944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185949 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d185949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185950 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d185950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17188 (p : Pattern) (selected : d185956 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185947 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17186 q selected
    | true =>
      simp only [d185947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185948 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185951 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17187 q selected
    | true =>
      simp only [d185951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185952 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185953 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185954 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185955 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185956 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro17189 (p : Pattern) (selected : d185960 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185951 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17187 q selected
    | true =>
      simp only [d185951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185952 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185957 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185958 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185959 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185960 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17190 (p : Pattern) (selected : d185972 p = 1) : d187591 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185907 q = 1) : d185907 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d185916 q = 1) : d185916 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d185934 q = 1) : d185934 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d185961 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17188 q selected
    | true =>
      simp only [d185961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17189 q selected
  have h5 (q : Pattern) (selected : d185962 q = 1) : d187587 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185962, d187587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185962, d187587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185968 q = 1) : d185968 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d185969 q = 1) : d187588 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185969, d187588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185969, d187588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185970 q = 1) : d187589 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185970, d187589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185970, d187589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d185971 q = 1) : d187590 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185971, d187590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185971, d187590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185972 q = 1) : d187591 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185972, d187591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185972, d187591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro17191 (p : Pattern) (selected : d185986 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185947 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17186 q selected
    | true =>
      simp only [d185947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185948 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185951 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17187 q selected
    | true =>
      simp only [d185951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185952 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185953 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185954 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d185955 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d185986 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d185986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17192 (p : Pattern) (selected : d185987 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185951 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d185951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17187 q selected
    | true =>
      simp only [d185951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d185952 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d185952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d185957 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d185957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185958 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d185959 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d185959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d185987 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d185987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d185987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17193 (p : Pattern) (selected : d185996 p = 1) : d187596 p = 1 := by
  have h0 (q : Pattern) (selected : d185907 q = 1) : d185907 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185916 q = 1) : d185916 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d185934 q = 1) : d185934 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d185961 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17188 q selected
    | true =>
      simp only [d185961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17189 q selected
  have h4 (q : Pattern) (selected : d185962 q = 1) : d187587 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185962, d187587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d185962, d187587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d185968 q = 1) : d185968 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d185969 q = 1) : d187588 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185969, d187588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d185969, d187588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185970 q = 1) : d187589 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185970, d187589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185970, d187589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d185971 q = 1) : d187590 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185971, d187590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185971, d187590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d185978 q = 1) : d185978 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d185983 q = 1) : d185983 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d185985 q = 1) : d185985 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d185988 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17191 q selected
    | true =>
      simp only [d185988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17192 q selected
  have h13 (q : Pattern) (selected : d185989 q = 1) : d187592 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185989, d187592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d185989, d187592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d185992 q = 1) : d185992 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d185993 q = 1) : d187593 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185993, d187593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d185993, d187593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d185994 q = 1) : d187594 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d185994, d187594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d185994, d187594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d185995 q = 1) : d187595 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d185995, d187595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d185995, d187595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d185996 q = 1) : d187596 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d185996, d187596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d185996, d187596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro17194 (p : Pattern) (selected : d186016 p = 1) : d187603 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185985 q = 1) : d185985 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d185988 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d185988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17191 q selected
    | true =>
      simp only [d185988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17192 q selected
  have h3 (q : Pattern) (selected : d185989 q = 1) : d187592 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d185989, d187592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185989, d187592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185992 q = 1) : d185992 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d185993 q = 1) : d187593 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d185993, d187593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185993, d187593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d186014 q = 1) : d187601 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d186014, d187601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186014, d187601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d186015 q = 1) : d187602 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d186015, d187602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186015, d187602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d186016 q = 1) : d187603 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d186016, d187603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186016, d187603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro17195 (p : Pattern) (selected : d186064 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d17430 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6872 q selected
  have h2 (q : Pattern) (selected : d10458 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6872 q selected
    | true =>
      simp only [d10458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d17431 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d17431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10460 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17432 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15835 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6874 q selected
  have h7 (q : Pattern) (selected : d10482 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6874 q selected
    | true =>
      simp only [d10482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15836 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10484 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d15837 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d15837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d186064 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d186064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d186064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro17196 (p : Pattern) (selected : d186065 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d17437 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6876 q selected
  have h2 (q : Pattern) (selected : d10493 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6876 q selected
    | true =>
      simp only [d10493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d17438 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d17438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10495 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17439 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d186065 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d186065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d186065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17197 (p : Pattern) (selected : d186075 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d186066 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d186066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17195 q selected
    | true =>
      simp only [d186066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17196 q selected
  have h2 (q : Pattern) (selected : d186067 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d186067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d186068 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d186068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d186069 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d186069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17196 q selected
    | true =>
      simp only [d186069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d186070 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d186070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d186071 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d186071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d186072 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d186072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d186072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d186073 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d186073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d186073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d186074 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d186074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d186074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d186075 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d186075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d186075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro17198 (p : Pattern) (selected : d186079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d186069 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d186069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17196 q selected
    | true =>
      simp only [d186069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d186070 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d186070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d186071 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d186071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d186073 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d186073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d186073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d186078 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d186078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d186078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d186079 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d186079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d186079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17199 (p : Pattern) (selected : d186085 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d186076 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d186076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17197 q selected
    | true =>
      simp only [d186076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d186077 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d186077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d186080 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d186080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17198 q selected
    | true =>
      simp only [d186080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d186081 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d186081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d186082 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d186082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d186082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d186083 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d186083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d186083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d186084 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d186084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d186084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d186085 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d186085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d186085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17200 (p : Pattern) (selected : d186089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d186080 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d186080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17198 q selected
    | true =>
      simp only [d186080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d186081 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d186081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d186086 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d186086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d186086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d186087 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d186087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d186087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d186088 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d186088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d186088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d186089 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d186089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d186089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17201 (p : Pattern) (selected : d186101 p = 1) : d187613 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d186063 q = 1) : d186063 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d186090 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d186090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17199 q selected
    | true =>
      simp only [d186090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17200 q selected
  have h3 (q : Pattern) (selected : d186091 q = 1) : d187609 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d186091, d187609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d186091, d187609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d186097 q = 1) : d186097 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d186098 q = 1) : d187610 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d186098, d187610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d186098, d187610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d186099 q = 1) : d187611 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d186099, d187611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186099, d187611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d186100 q = 1) : d187612 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d186100, d187612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186100, d187612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d186101 q = 1) : d187613 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d186101, d187613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186101, d187613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro17202 (p : Pattern) (selected : d186118 p = 1) : d187619 p = 1 := by
  have h0 (q : Pattern) (selected : d185899 q = 1) : d185899 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d185997 q = 1) : d187597 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d185997, d187597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17190 q selected
    | true =>
      simp only [d185997, d187597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17193 q selected
  have h2 (q : Pattern) (selected : d186010 q = 1) : d186010 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d186011 q = 1) : d187598 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d186011, d187598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d186011, d187598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d186012 q = 1) : d187599 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d186012, d187599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d186012, d187599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d186013 q = 1) : d187600 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d186013, d187600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186013, d187600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d186017 q = 1) : d187604 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d186017, d187604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d186017, d187604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17194 q selected
  have h8 (q : Pattern) (selected : d186019 q = 1) : d186019 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d186020 q = 1) : d187605 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d186020, d187605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d186020, d187605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d186021 q = 1) : d187606 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d186021, d187606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d186021, d187606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d186022 q = 1) : d187607 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d186022, d187607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d186022, d187607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d186023 q = 1) : d187608 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d186023, d187608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d186023, d187608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d186102 q = 1) : d187614 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d186102, d187614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d186102, d187614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17201 q selected
  have h14 (q : Pattern) (selected : d186113 q = 1) : d186113 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d186114 q = 1) : d187615 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d186114, d187615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d186114, d187615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d186115 q = 1) : d187616 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d186115, d187616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d186115, d187616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d186116 q = 1) : d187617 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d186116, d187617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d186116, d187617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d186117 q = 1) : d187618 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d186117, d187618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d186117, d187618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d186118 q = 1) : d187619 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d186118, d187619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d186118, d187619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro17203 (p : Pattern) (selected : d186124 p = 1) : d187625 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d186119 q = 1) : d187620 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d186119, d187620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186119, d187620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17202 q selected
  have h2 (q : Pattern) (selected : d186120 q = 1) : d187621 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d186120, d187621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186120, d187621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d186121 q = 1) : d187622 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d186121, d187622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186121, d187622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d186122 q = 1) : d187623 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d186122, d187623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186122, d187623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d186123 q = 1) : d187624 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d186123, d187624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186123, d187624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d186124 q = 1) : d187625 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d186124, d187625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d186124, d187625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17204 (p : Pattern) (selected : d186130 p = 1) : d187631 p = 1 := by
  have h0 (q : Pattern) (selected : d185043 q = 1) : d187460 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d185043, d187460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17110 q selected
    | true =>
      simp only [d185043, d187460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17123 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d185306 q = 1) : d187500 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d185306, d187500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185306, d187500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17143 q selected
  have h3 (q : Pattern) (selected : d185307 q = 1) : d187501 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d185307, d187501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d185307, d187501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d185578 q = 1) : d187541 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d185578, d187541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185578, d187541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17163 q selected
  have h5 (q : Pattern) (selected : d185579 q = 1) : d187542 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d185579, d187542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185579, d187542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d185580 q = 1) : d187543 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d185580, d187543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185580, d187543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d185851 q = 1) : d187583 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d185851, d187583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185851, d187583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17183 q selected
  have h8 (q : Pattern) (selected : d185852 q = 1) : d187584 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d185852, d187584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185852, d187584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d185853 q = 1) : d187585 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d185853, d187585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d185853, d187585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d185854 q = 1) : d187586 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d185854, d187586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d185854, d187586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d186125 q = 1) : d187626 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d186125, d187626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d186125, d187626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17203 q selected
  have h12 (q : Pattern) (selected : d186126 q = 1) : d187627 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d186126, d187627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d186126, d187627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d186127 q = 1) : d187628 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d186127, d187628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d186127, d187628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d186128 q = 1) : d187629 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d186128, d187629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d186128, d187629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d186129 q = 1) : d187630 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d186129, d187630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d186129, d187630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d186130 q = 1) : d187631 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d186130, d187631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d186130, d187631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro17205 (p : Pattern) (selected : d186136 p = 1) : d187637 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d186131 q = 1) : d187632 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d186131, d187632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17204 q selected
    | true =>
      simp only [d186131, d187632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d186132 q = 1) : d187633 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d186132, d187633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d186132, d187633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d186133 q = 1) : d187634 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d186133, d187634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d186133, d187634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d186134 q = 1) : d187635 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d186134, d187635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d186134, d187635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d186135 q = 1) : d187636 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d186135, d187636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d186135, d187636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d186136 q = 1) : d187637 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d186136, d187637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d186136, d187637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17206 (p : Pattern) (selected : d186142 p = 1) : d187643 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d186137 q = 1) : d187638 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d186137, d187638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17205 q selected
    | true =>
      simp only [d186137, d187638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d186138 q = 1) : d187639 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d186138, d187639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d186138, d187639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d186139 q = 1) : d187640 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d186139, d187640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d186139, d187640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d186140 q = 1) : d187641 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d186140, d187641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d186140, d187641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d186141 q = 1) : d187642 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d186141, d187642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d186141, d187642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d186142 q = 1) : d187643 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d186142, d187643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d186142, d187643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17207 (p : Pattern) (selected : d186148 p = 1) : d187649 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d186143 q = 1) : d187644 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d186143, d187644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17206 q selected
    | true =>
      simp only [d186143, d187644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d186144 q = 1) : d187645 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d186144, d187645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d186144, d187645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d186145 q = 1) : d187646 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d186145, d187646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d186145, d187646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d186146 q = 1) : d187647 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d186146, d187647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d186146, d187647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d186147 q = 1) : d187648 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d186147, d187648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d186147, d187648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d186148 q = 1) : d187649 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d186148, d187649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d186148, d187649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17208 (p : Pattern) (selected : d186154 p = 1) : d187655 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d186149 q = 1) : d187650 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d186149, d187650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17207 q selected
    | true =>
      simp only [d186149, d187650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d186150 q = 1) : d187651 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d186150, d187651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d186150, d187651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d186151 q = 1) : d187652 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d186151, d187652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d186151, d187652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d186152 q = 1) : d187653 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d186152, d187653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d186152, d187653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d186153 q = 1) : d187654 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d186153, d187654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d186153, d187654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d186154 q = 1) : d187655 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d186154, d187655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d186154, d187655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17209 (p : Pattern) (selected : d186160 p = 1) : d187661 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d186155 q = 1) : d187656 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d186155, d187656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17208 q selected
    | true =>
      simp only [d186155, d187656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d186156 q = 1) : d187657 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d186156, d187657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d186156, d187657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d186157 q = 1) : d187658 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d186157, d187658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d186157, d187658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d186158 q = 1) : d187659 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d186158, d187659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d186158, d187659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d186159 q = 1) : d187660 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d186159, d187660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d186159, d187660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d186160 q = 1) : d187661 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d186160, d187661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d186160, d187661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17210 (p : Pattern) (selected : d186166 p = 1) : d187667 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d186161 q = 1) : d187662 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d186161, d187662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17209 q selected
    | true =>
      simp only [d186161, d187662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d186162 q = 1) : d187663 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d186162, d187663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d186162, d187663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d186163 q = 1) : d187664 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d186163, d187664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d186163, d187664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d186164 q = 1) : d187665 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d186164, d187665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d186164, d187665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d186165 q = 1) : d187666 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d186165, d187666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d186165, d187666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d186166 q = 1) : d187667 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d186166, d187667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d186166, d187667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17211 (p : Pattern) (selected : d186172 p = 1) : d187673 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d186167 q = 1) : d187668 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d186167, d187668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17210 q selected
    | true =>
      simp only [d186167, d187668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d186168 q = 1) : d187669 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d186168, d187669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d186168, d187669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d186169 q = 1) : d187670 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d186169, d187670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d186169, d187670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d186170 q = 1) : d187671 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d186170, d187671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d186170, d187671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d186171 q = 1) : d187672 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d186171, d187672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d186171, d187672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d186172 q = 1) : d187673 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d186172, d187673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d186172, d187673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17212 (p : Pattern) (selected : d18538 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d66 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro645 q selected
  have h2 (q : Pattern) (selected : d18534 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d18534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d25 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro645 q selected
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d26 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18535 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18536 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d18537 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d18538 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d18538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17213 (p : Pattern) (selected : d18548 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18539 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17212 q selected
    | true =>
      simp only [d18539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18540 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18541 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18542 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18543 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d31 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro646 q selected
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d18544 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d18545 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d18546 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d18546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d18547 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d18547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d18548 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro17214 (p : Pattern) (selected : d18554 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18549 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17213 q selected
    | true =>
      simp only [d18549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18550 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18551 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18552 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18553 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18554 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17215 (p : Pattern) (selected : d18560 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18555 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17214 q selected
    | true =>
      simp only [d18555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18556 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d18556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d18557 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18558 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d18559 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18560 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17216 (p : Pattern) (selected : d18566 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18561 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17215 q selected
  have h2 (q : Pattern) (selected : d18562 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d18562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d18562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d18563 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d18563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18564 q = 2) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d18564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18565 q = 2) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d18565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18566 q = 2) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d18566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17217 (p : Pattern) (selected : d18575 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d226 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro663 q selected
  have h2 (q : Pattern) (selected : d18571 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d18571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d139 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro663 q selected
    | true =>
      simp only [d139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d140 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18572 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18573 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d66 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro645 q selected
  have h8 (q : Pattern) (selected : d18534 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d18534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d25 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro645 q selected
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d26 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d18535 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d18535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d18536 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d18536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d18574 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d18537 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d18537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d18575 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d18575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro17218 (p : Pattern) (selected : d18585 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18576 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17217 q selected
    | true =>
      simp only [d18576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17212 q selected
  have h2 (q : Pattern) (selected : d18577 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18578 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18539 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17212 q selected
    | true =>
      simp only [d18539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18540 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18541 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d18579 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d18542 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d18580 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d18580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d145 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro664 q selected
    | true =>
      simp only [d145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro646 q selected
  have h11 (q : Pattern) (selected : d18581 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d18581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d18582 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d31 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro646 q selected
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d18544 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d18544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d18545 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d18583 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d18583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d18546 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d18546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d18584 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d18584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d18585 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d18585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro17219 (p : Pattern) (selected : d18591 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18586 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17218 q selected
    | true =>
      simp only [d18586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18587 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18549 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17213 q selected
    | true =>
      simp only [d18549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18550 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d18588 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18589 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d18590 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d18591 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d18591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17220 (p : Pattern) (selected : d18597 p = 2) : d18538 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d245 q = 2) : d66 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d245, d66, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d245, d66, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro668 q selected
  have h2 (q : Pattern) (selected : d18593 q = 2) : d18534 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18593, d18534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d18593, d18534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d170 q = 2) : d25 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, d25, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro668 q selected
    | true =>
      simp only [d170, d25, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d171 q = 2) : d26 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d171, d26, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d171, d26, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18594 q = 2) : d18535 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18594, d18535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18594, d18535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18595 q = 2) : d18536 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18595, d18536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18595, d18536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d18596 q = 2) : d18537 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18596, d18537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18596, d18537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d18597 q = 2) : d18538 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18597, d18538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d18597, d18538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17221 (p : Pattern) (selected : d18607 p = 2) : d18548 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18598 q = 2) : d18539 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18598, d18539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17220 q selected
    | true =>
      simp only [d18598, d18539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18599 q = 2) : d18540 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18599, d18540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18599, d18540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18600 q = 2) : d18541 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18600, d18541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18600, d18541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18601 q = 2) : d18542 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18601, d18542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18601, d18542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18602 q = 2) : d18543 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18602, d18543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18602, d18543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176 q = 2) : d31 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176, d31, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro669 q selected
    | true =>
      simp only [d176, d31, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d18603 q = 2) : d18544 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18603, d18544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18603, d18544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d18604 q = 2) : d18545 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18604, d18545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18604, d18545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d18605 q = 2) : d18546 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18605, d18546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d18605, d18546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d18606 q = 2) : d18547 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18606, d18547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d18606, d18547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d18607 q = 2) : d18548 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18607, d18548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18607, d18548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro17222 (p : Pattern) (selected : d18613 p = 2) : d18554 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18608 q = 2) : d18549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18608, d18549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17221 q selected
    | true =>
      simp only [d18608, d18549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18609 q = 2) : d18550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18609, d18550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18609, d18550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18610 q = 2) : d18551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18610, d18551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18610, d18551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18611 q = 2) : d18552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18611, d18552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18611, d18552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18612 q = 2) : d18553 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18612, d18553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18612, d18553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18613 q = 2) : d18554 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18613, d18554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18613, d18554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17223 (p : Pattern) (selected : d18619 p = 2) : d18695 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18592 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17219 q selected
    | true =>
      simp only [d18592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17214 q selected
  have h2 (q : Pattern) (selected : d18614 q = 2) : d18555 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18614, d18555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17222 q selected
    | true =>
      simp only [d18614, d18555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d18615 q = 2) : d18691 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18615, d18691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d18615, d18691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18555 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17214 q selected
    | true =>
      simp only [d18555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18556 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18616 q = 2) : d18692 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18616, d18692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18616, d18692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d18617 q = 2) : d18693 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18617, d18693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18617, d18693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d18618 q = 2) : d18694 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18618, d18694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18618, d18694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d18619 q = 2) : d18695 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18619, d18695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18619, d18695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro17224 (p : Pattern) (selected : d18625 p = 2) : d187684 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18620 q = 2) : d18696 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18620, d18696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18620, d18696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17223 q selected
  have h2 (q : Pattern) (selected : d18621 q = 2) : d187680 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d18621, d187680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d18621, d187680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d18622 q = 2) : d187681 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d18622, d187681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18622, d187681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18623 q = 2) : d187682 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d18623, d187682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18623, d187682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18624 q = 2) : d187683 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d18624, d187683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18624, d187683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18625 q = 2) : d187684 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d18625, d187684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18625, d187684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17225 (p : Pattern) (selected : d18639 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d412 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro693 q selected
  have h2 (q : Pattern) (selected : d18631 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d18631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d319 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro693 q selected
    | true =>
      simp only [d319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d320 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18632 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18633 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d226 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro663 q selected
  have h8 (q : Pattern) (selected : d18571 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d18571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d139 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro663 q selected
    | true =>
      simp only [d139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d140 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d18572 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d18572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d18573 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d18573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d18634 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d12599 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10492 q selected
  have h15 (q : Pattern) (selected : d18635 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d18635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d9382 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10492 q selected
    | true =>
      simp only [d9382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d9384 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d9384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d18636 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d18636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d18637 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d18637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d66 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro645 q selected
  have h21 (q : Pattern) (selected : d18534 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d18534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d25 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro645 q selected
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d26 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d18535 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d18535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d18536 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d18536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d18638 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d18638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d18639 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d18639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro17226 (p : Pattern) (selected : d18649 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18640 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17225 q selected
    | true =>
      simp only [d18640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17217 q selected
  have h2 (q : Pattern) (selected : d18641 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18642 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18576 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17217 q selected
    | true =>
      simp only [d18576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17212 q selected
  have h5 (q : Pattern) (selected : d18577 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18578 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d18643 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d18539 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17212 q selected
    | true =>
      simp only [d18539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d18540 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d18541 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d18579 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d18644 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d18644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d15967 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15239 q selected
    | true =>
      simp only [d15967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro664 q selected
  have h14 (q : Pattern) (selected : d18645 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d18645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d18646 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d145 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro664 q selected
    | true =>
      simp only [d145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro646 q selected
  have h17 (q : Pattern) (selected : d18581 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d18581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d18582 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d18647 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d18647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d31 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro646 q selected
    | true =>
      simp only [d31, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d18544 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d18544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d18545 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d18583 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d18583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  have h24 (q : Pattern) (selected : d18648 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d18648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d18649 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d18649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  exact h25 p selected
theorem eqIntro17227 (p : Pattern) (selected : d18655 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18650 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17226 q selected
    | true =>
      simp only [d18650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18651 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18586 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17218 q selected
    | true =>
      simp only [d18586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18587 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d18652 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18653 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d18654 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d18655 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d18655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17228 (p : Pattern) (selected : d18661 p = 2) : d18575 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d431 q = 2) : d226 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d431, d226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d431, d226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro698 q selected
  have h2 (q : Pattern) (selected : d18657 q = 2) : d18571 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18657, d18571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d18657, d18571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d350 q = 2) : d139 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d350, d139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro698 q selected
    | true =>
      simp only [d350, d139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d351 q = 2) : d140 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351, d140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d351, d140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18658 q = 2) : d18572 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18658, d18572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18658, d18572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18659 q = 2) : d18573 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18659, d18573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18659, d18573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d245 q = 2) : d66 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d245, d66, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d245, d66, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro668 q selected
  have h8 (q : Pattern) (selected : d18593 q = 2) : d18534 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18593, d18534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d18593, d18534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d170 q = 2) : d25 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, d25, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro668 q selected
    | true =>
      simp only [d170, d25, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d171 q = 2) : d26 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d171, d26, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d171, d26, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d18594 q = 2) : d18535 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18594, d18535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d18594, d18535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d18595 q = 2) : d18536 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18595, d18536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d18595, d18536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d18660 q = 2) : d18574 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18660, d18574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18660, d18574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d18596 q = 2) : d18537 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18596, d18537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d18596, d18537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d18661 q = 2) : d18575 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18661, d18575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d18661, d18575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro17229 (p : Pattern) (selected : d18671 p = 2) : d18585 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18662 q = 2) : d18576 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18662, d18576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17228 q selected
    | true =>
      simp only [d18662, d18576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17220 q selected
  have h2 (q : Pattern) (selected : d18663 q = 2) : d18577 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18663, d18577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18663, d18577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18664 q = 2) : d18578 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18664, d18578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18664, d18578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18598 q = 2) : d18539 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18598, d18539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17220 q selected
    | true =>
      simp only [d18598, d18539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18599 q = 2) : d18540 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18599, d18540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18599, d18540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18600 q = 2) : d18541 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18600, d18541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18600, d18541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d18665 q = 2) : d18579 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18665, d18579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18665, d18579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d18601 q = 2) : d18542 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18601, d18542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18601, d18542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d18666 q = 2) : d18580 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18666, d18580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d18666, d18580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d356 q = 2) : d145 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d356, d145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro699 q selected
    | true =>
      simp only [d356, d145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro669 q selected
  have h11 (q : Pattern) (selected : d18667 q = 2) : d18581 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18667, d18581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d18667, d18581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d18668 q = 2) : d18582 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18668, d18582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18668, d18582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d176 q = 2) : d31 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176, d31, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro669 q selected
    | true =>
      simp only [d176, d31, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d18603 q = 2) : d18544 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18603, d18544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d18603, d18544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d18604 q = 2) : d18545 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18604, d18545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18604, d18545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d18669 q = 2) : d18583 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18669, d18583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d18669, d18583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d18605 q = 2) : d18546 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18605, d18546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d18605, d18546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d18670 q = 2) : d18584 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18670, d18584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d18670, d18584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d18671 q = 2) : d18585 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18671, d18585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d18671, d18585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro17230 (p : Pattern) (selected : d18677 p = 2) : d18591 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18672 q = 2) : d18586 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18672, d18586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17229 q selected
    | true =>
      simp only [d18672, d18586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18673 q = 2) : d18587 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18673, d18587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18673, d18587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18608 q = 2) : d18549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18608, d18549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17221 q selected
    | true =>
      simp only [d18608, d18549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18609 q = 2) : d18550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18609, d18550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18609, d18550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d18674 q = 2) : d18588 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18674, d18588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18674, d18588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18675 q = 2) : d18589 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18675, d18589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18675, d18589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d18676 q = 2) : d18590 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18676, d18590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18676, d18590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d18677 q = 2) : d18591 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18677, d18591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d18677, d18591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17231 (p : Pattern) (selected : d18683 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18586 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17218 q selected
    | true =>
      simp only [d18586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18587 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18680 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18681 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18682 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18683 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17232 (p : Pattern) (selected : d18689 p = 2) : d187694 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18656 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17227 q selected
    | true =>
      simp only [d18656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17219 q selected
  have h2 (q : Pattern) (selected : d18678 q = 2) : d18592 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18678, d18592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17230 q selected
    | true =>
      simp only [d18678, d18592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17222 q selected
  have h3 (q : Pattern) (selected : d18679 q = 2) : d187690 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18679, d187690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d18679, d187690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18684 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17231 q selected
    | true =>
      simp only [d18684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18685 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18686 q = 2) : d187691 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18686, d187691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18686, d187691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d18687 q = 2) : d187692 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18687, d187692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18687, d187692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d18688 q = 2) : d187693 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18688, d187693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18688, d187693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d18689 q = 2) : d187694 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18689, d187694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18689, d187694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro17233 (p : Pattern) (selected : d18695 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18555 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17214 q selected
    | true =>
      simp only [d18555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18691 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18692 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18693 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d18694 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18695 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro17234 (p : Pattern) (selected : d18701 p = 2) : d187700 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18690 q = 2) : d187695 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18690, d187695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18690, d187695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17232 q selected
  have h2 (q : Pattern) (selected : d18696 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17233 q selected
  have h3 (q : Pattern) (selected : d18697 q = 2) : d187696 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d18697, d187696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d18697, d187696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18698 q = 2) : d187697 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d18698, d187697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18698, d187697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18699 q = 2) : d187698 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d18699, d187698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18699, d187698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18700 q = 2) : d187699 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d18700, d187699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18700, d187699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d18701 q = 2) : d187700 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d18701, d187700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18701, d187700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro17235 (p : Pattern) (selected : d18707 p = 2) : d187706 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18567 q = 2) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d18567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17216 q selected
  have h2 (q : Pattern) (selected : d18568 q = 2) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d18568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18569 q = 2) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d18569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18570 q = 2) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d18570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d18626 q = 2) : d187685 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d18626, d187685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18626, d187685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17224 q selected
  have h6 (q : Pattern) (selected : d18627 q = 2) : d187686 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d18627, d187686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18627, d187686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d18628 q = 2) : d187687 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d18628, d187687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18628, d187687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d18629 q = 2) : d187688 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d18629, d187688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18629, d187688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d18630 q = 2) : d187689 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d18630, d187689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18630, d187689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d18702 q = 2) : d187701 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d18702, d187701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18702, d187701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17234 q selected
  have h11 (q : Pattern) (selected : d18703 q = 2) : d187702 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d18703, d187702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18703, d187702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d18704 q = 2) : d187703 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d18704, d187703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18704, d187703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d18705 q = 2) : d187704 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d18705, d187704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18705, d187704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d18706 q = 2) : d187705 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d18706, d187705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18706, d187705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d18707 q = 2) : d187706 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d18707, d187706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d18707, d187706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro17236 (p : Pattern) (selected : d18719 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d659 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro735 q selected
  have h2 (q : Pattern) (selected : d18708 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d18708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d543 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro735 q selected
    | true =>
      simp only [d543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d544 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18709 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18710 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d16156 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10504 q selected
  have h8 (q : Pattern) (selected : d18711 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d18711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d9458 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10504 q selected
    | true =>
      simp only [d9458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d9460 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d9460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d18712 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d18712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d18713 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d18713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d18714 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d12858 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10505 q selected
  have h15 (q : Pattern) (selected : d18715 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d18715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d9468 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10505 q selected
    | true =>
      simp only [d9468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d9470 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d9470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d18716 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d18716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d18717 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d18717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d12599 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10492 q selected
  have h21 (q : Pattern) (selected : d18635 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d18635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d9382 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10492 q selected
    | true =>
      simp only [d9382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d9384 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d9384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d18636 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d18636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d18637 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d18637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d18718 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d18718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d18719 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d18719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro17237 (p : Pattern) (selected : d18723 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d12599 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10492 q selected
  have h2 (q : Pattern) (selected : d18635 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d18635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d9382 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10492 q selected
    | true =>
      simp only [d9382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d9384 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d9384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18636 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18637 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d66 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro645 q selected
  have h8 (q : Pattern) (selected : d18534 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d18534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d25 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro645 q selected
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d26 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d26, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d18535 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d18535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d18536 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d18536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d18638 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d18537 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d18537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d18723 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d18723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro17238 (p : Pattern) (selected : d18735 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18720 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17236 q selected
    | true =>
      simp only [d18720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17225 q selected
  have h2 (q : Pattern) (selected : d18721 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18722 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18724 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17225 q selected
    | true =>
      simp only [d18724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17237 q selected
  have h5 (q : Pattern) (selected : d18725 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18726 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d18727 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d18640 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17225 q selected
    | true =>
      simp only [d18640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17217 q selected
  have h9 (q : Pattern) (selected : d18641 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d18642 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d18576 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17217 q selected
    | true =>
      simp only [d18576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17212 q selected
  have h12 (q : Pattern) (selected : d18577 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d18578 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d18643 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d18643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d18728 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d18728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d16078 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15259 q selected
    | true =>
      simp only [d16078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15239 q selected
  have h17 (q : Pattern) (selected : d18729 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d18729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d18730 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d16082 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15239 q selected
    | true =>
      simp only [d16082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15260 q selected
  have h20 (q : Pattern) (selected : d18731 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d18731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d18732 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d18733 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d18733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d15967 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15239 q selected
    | true =>
      simp only [d15967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro664 q selected
  have h24 (q : Pattern) (selected : d18645 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d18645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d18646 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d145 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro664 q selected
    | true =>
      simp only [d145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro646 q selected
  have h27 (q : Pattern) (selected : d18581 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d18581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d18582 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d18647 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d18647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d18734 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d18734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d18735 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d18735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro17239 (p : Pattern) (selected : d18742 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18640 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17225 q selected
    | true =>
      simp only [d18640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17217 q selected
  have h2 (q : Pattern) (selected : d18641 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18642 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18576 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17217 q selected
    | true =>
      simp only [d18576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17212 q selected
  have h5 (q : Pattern) (selected : d18577 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18578 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d18643 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d18738 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d18739 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d18739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d15967 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15239 q selected
    | true =>
      simp only [d15967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro664 q selected
  have h11 (q : Pattern) (selected : d18645 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d18645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d18646 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d145 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro664 q selected
    | true =>
      simp only [d145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro646 q selected
  have h14 (q : Pattern) (selected : d18581 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d18581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d18582 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d18647 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d18647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d18740 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d18740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d18741 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d18741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d18742 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d18742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro17240 (p : Pattern) (selected : d18748 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18736 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17238 q selected
    | true =>
      simp only [d18736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18737 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18743 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17239 q selected
    | true =>
      simp only [d18743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18744 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d18745 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18746 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d18747 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d18748 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d18748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17241 (p : Pattern) (selected : d18751 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18576 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17217 q selected
    | true =>
      simp only [d18576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17212 q selected
  have h2 (q : Pattern) (selected : d18577 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18578 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18738 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18749 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d145 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro664 q selected
    | true =>
      simp only [d145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro646 q selected
  have h7 (q : Pattern) (selected : d18581 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d18582 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d18740 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d18740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d18750 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d18750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d18751 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro17242 (p : Pattern) (selected : d18757 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18743 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17239 q selected
    | true =>
      simp only [d18743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18744 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18752 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17241 q selected
    | true =>
      simp only [d18752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18753 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d18754 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18755 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d18756 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d18757 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d18757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17243 (p : Pattern) (selected : d18767 p = 2) : d18639 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d691 q = 2) : d412 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d691, d412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d691, d412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro740 q selected
  have h2 (q : Pattern) (selected : d18759 q = 2) : d18631 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18759, d18631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d18759, d18631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d574 q = 2) : d319 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d574, d319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro740 q selected
    | true =>
      simp only [d574, d319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d575 q = 2) : d320 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d575, d320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d575, d320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18760 q = 2) : d18632 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18760, d18632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18760, d18632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18761 q = 2) : d18633 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18761, d18633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18761, d18633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d431 q = 2) : d226 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d431, d226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d431, d226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro698 q selected
  have h8 (q : Pattern) (selected : d18657 q = 2) : d18571 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18657, d18571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d18657, d18571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d350 q = 2) : d139 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d350, d139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro698 q selected
    | true =>
      simp only [d350, d139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d351 q = 2) : d140 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351, d140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d351, d140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d18658 q = 2) : d18572 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18658, d18572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d18658, d18572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d18659 q = 2) : d18573 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18659, d18573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d18659, d18573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d18762 q = 2) : d18634 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18762, d18634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18762, d18634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d14404 q = 2) : d12599 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14404, d12599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14404, d12599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10513 q selected
  have h15 (q : Pattern) (selected : d18763 q = 2) : d18635 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18763, d18635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d18763, d18635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d9512 q = 2) : d9382 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9512, d9382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10513 q selected
    | true =>
      simp only [d9512, d9382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d9514 q = 2) : d9384 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9514, d9384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d9514, d9384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d18764 q = 2) : d18636 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18764, d18636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d18764, d18636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d18765 q = 2) : d18637 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18765, d18637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d18765, d18637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d245 q = 2) : d66 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d245, d66, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d245, d66, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro668 q selected
  have h21 (q : Pattern) (selected : d18593 q = 2) : d18534 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18593, d18534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d18593, d18534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d170 q = 2) : d25 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, d25, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro668 q selected
    | true =>
      simp only [d170, d25, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d171 q = 2) : d26 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d171, d26, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d171, d26, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d18594 q = 2) : d18535 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18594, d18535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d18594, d18535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d18595 q = 2) : d18536 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18595, d18536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d18595, d18536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d18766 q = 2) : d18638 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18766, d18638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d18766, d18638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d18767 q = 2) : d18639 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18767, d18639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d18767, d18639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro17244 (p : Pattern) (selected : d18779 p = 2) : d18742 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18768 q = 2) : d18640 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18768, d18640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17243 q selected
    | true =>
      simp only [d18768, d18640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17228 q selected
  have h2 (q : Pattern) (selected : d18769 q = 2) : d18641 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18769, d18641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18769, d18641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18770 q = 2) : d18642 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18770, d18642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18770, d18642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18662 q = 2) : d18576 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18662, d18576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17228 q selected
    | true =>
      simp only [d18662, d18576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17220 q selected
  have h5 (q : Pattern) (selected : d18663 q = 2) : d18577 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18663, d18577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18663, d18577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18664 q = 2) : d18578 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18664, d18578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18664, d18578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d18771 q = 2) : d18643 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18771, d18643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18771, d18643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d18772 q = 2) : d18738 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18772, d18738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18772, d18738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d18773 q = 2) : d18739 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18773, d18739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d18773, d18739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d16097 q = 2) : d15967 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16097, d15967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15263 q selected
    | true =>
      simp only [d16097, d15967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro699 q selected
  have h11 (q : Pattern) (selected : d18774 q = 2) : d18645 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18774, d18645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d18774, d18645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d18775 q = 2) : d18646 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18775, d18646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18775, d18646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d356 q = 2) : d145 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d356, d145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro699 q selected
    | true =>
      simp only [d356, d145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro669 q selected
  have h14 (q : Pattern) (selected : d18667 q = 2) : d18581 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18667, d18581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d18667, d18581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d18668 q = 2) : d18582 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18668, d18582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18668, d18582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d18776 q = 2) : d18647 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18776, d18647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d18776, d18647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d18777 q = 2) : d18740 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18777, d18740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d18777, d18740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d18778 q = 2) : d18741 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18778, d18741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d18778, d18741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d18779 q = 2) : d18742 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18779, d18742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d18779, d18742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro17245 (p : Pattern) (selected : d18784 p = 2) : d18751 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18662 q = 2) : d18576 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18662, d18576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17228 q selected
    | true =>
      simp only [d18662, d18576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17220 q selected
  have h2 (q : Pattern) (selected : d18663 q = 2) : d18577 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18663, d18577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18663, d18577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18664 q = 2) : d18578 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18664, d18578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18664, d18578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18772 q = 2) : d18738 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18772, d18738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18772, d18738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18782 q = 2) : d18749 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18782, d18749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18782, d18749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d356 q = 2) : d145 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d356, d145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro699 q selected
    | true =>
      simp only [d356, d145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro669 q selected
  have h7 (q : Pattern) (selected : d18667 q = 2) : d18581 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18667, d18581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18667, d18581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d18668 q = 2) : d18582 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18668, d18582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18668, d18582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d18777 q = 2) : d18740 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18777, d18740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d18777, d18740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d18783 q = 2) : d18750 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18783, d18750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d18783, d18750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d18784 q = 2) : d18751 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18784, d18751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18784, d18751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro17246 (p : Pattern) (selected : d18790 p = 2) : d18757 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18780 q = 2) : d18743 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18780, d18743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17244 q selected
    | true =>
      simp only [d18780, d18743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18781 q = 2) : d18744 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18781, d18744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18781, d18744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18785 q = 2) : d18752 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18785, d18752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17245 q selected
    | true =>
      simp only [d18785, d18752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18786 q = 2) : d18753 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18786, d18753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18786, d18753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d18787 q = 2) : d18754 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18787, d18754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18787, d18754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18788 q = 2) : d18755 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18788, d18755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18788, d18755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d18789 q = 2) : d18756 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18789, d18756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18789, d18756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d18790 q = 2) : d18757 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18790, d18757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d18790, d18757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro17247 (p : Pattern) (selected : d18794 p = 2) : d18811 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18785 q = 2) : d18752 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18785, d18752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17245 q selected
    | true =>
      simp only [d18785, d18752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18786 q = 2) : d18753 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18786, d18753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18786, d18753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18791 q = 2) : d18808 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18791, d18808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18791, d18808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18792 q = 2) : d18809 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18792, d18809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18792, d18809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18793 q = 2) : d18810 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18793, d18810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18793, d18810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18794 q = 2) : d18811 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18794, d18811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18794, d18811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17248 (p : Pattern) (selected : d18800 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18743 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17239 q selected
    | true =>
      simp only [d18743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18744 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18797 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18798 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18799 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18800 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro17249 (p : Pattern) (selected : d18806 p = 2) : d187712 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18758 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17240 q selected
    | true =>
      simp only [d18758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17242 q selected
  have h2 (q : Pattern) (selected : d18795 q = 2) : d187707 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18795, d187707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17246 q selected
    | true =>
      simp only [d18795, d187707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17247 q selected
  have h3 (q : Pattern) (selected : d18796 q = 2) : d187708 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18796, d187708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d18796, d187708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18801 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17248 q selected
    | true =>
      simp only [d18801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18802 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18803 q = 2) : d187709 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18803, d187709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18803, d187709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d18804 q = 2) : d187710 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18804, d187710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18804, d187710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d18805 q = 2) : d187711 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18805, d187711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18805, d187711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d18806 q = 2) : d187712 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18806, d187712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18806, d187712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
end NetHack.Soko22Hazard87
