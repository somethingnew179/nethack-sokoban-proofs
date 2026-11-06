import NetHack.Soko22Hazard87.EqIntroBlocks0064
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro16250 (p : Pattern) (selected : d176964 p = 0) : d177984 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176955 q = 0) : d177975 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176955, d177975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16248 q selected
    | true =>
      simp only [d176955, d177975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176956 q = 0) : d177976 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176956, d177976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176956, d177976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176961 q = 0) : d177981 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176961, d177981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176961, d177981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176962 q = 0) : d177982 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176962, d177982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176962, d177982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176963 q = 0) : d177983 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176963, d177983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176963, d177983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176964 q = 0) : d177984 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176964, d177984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176964, d177984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16251 (p : Pattern) (selected : d176972 p = 0) : d178040 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176868 q = 0) : d177961 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176868, d177961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16227 q selected
    | true =>
      simp only [d176868, d177961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16228 q selected
  have h2 (q : Pattern) (selected : d176869 q = 0) : d177962 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176869, d177962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176869, d177962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176870 q = 0) : d177963 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176870, d177963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176870, d177963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176871 q = 0) : d177964 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176871, d177964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16228 q selected
    | true =>
      simp only [d176871, d177964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16229 q selected
  have h5 (q : Pattern) (selected : d176872 q = 0) : d177965 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176872, d177965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176872, d177965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176873 q = 0) : d177966 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176873, d177966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176873, d177966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176874 q = 0) : d177967 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176874, d177967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176874, d177967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176967 q = 0) : d178035 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176967, d178035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16228 q selected
    | true =>
      simp only [d176967, d178035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d176968 q = 0) : d178036 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176968, d178036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176968, d178036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176969 q = 0) : d178037 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176969, d178037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176969, d178037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d176970 q = 0) : d178038 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176970, d178038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d176970, d178038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d176971 q = 0) : d178039 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176971, d178039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176971, d178039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d176972 q = 0) : d178040 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176972, d178040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d176972, d178040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro16252 (p : Pattern) (selected : d176978 p = 0) : d178046 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176973 q = 0) : d178041 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176973, d178041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16251 q selected
    | true =>
      simp only [d176973, d178041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176974 q = 0) : d178042 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176974, d178042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176974, d178042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176975 q = 0) : d178043 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176975, d178043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176975, d178043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176976 q = 0) : d178044 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176976, d178044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176976, d178044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176977 q = 0) : d178045 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176977, d178045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176977, d178045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176978 q = 0) : d178046 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176978, d178046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176978, d178046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16253 (p : Pattern) (selected : d176984 p = 0) : d178052 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176915 q = 0) : d178008 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176915, d178008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16238 q selected
    | true =>
      simp only [d176915, d178008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16239 q selected
  have h2 (q : Pattern) (selected : d176916 q = 0) : d178009 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176916, d178009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176916, d178009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176917 q = 0) : d178010 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176917, d178010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176917, d178010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176918 q = 0) : d178011 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176918, d178011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176918, d178011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176925 q = 0) : d178018 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176925, d178018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16240 q selected
    | true =>
      simp only [d176925, d178018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16241 q selected
  have h6 (q : Pattern) (selected : d176926 q = 0) : d178019 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176926, d178019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176926, d178019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176927 q = 0) : d178020 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176927, d178020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176927, d178020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176940 q = 0) : d178033 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176940, d178033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16243 q selected
    | true =>
      simp only [d176940, d178033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16232 q selected
  have h9 (q : Pattern) (selected : d176965 q = 0) : d177985 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176965, d177985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16249 q selected
    | true =>
      simp only [d176965, d177985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16250 q selected
  have h10 (q : Pattern) (selected : d176966 q = 0) : d178034 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176966, d178034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d176966, d178034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d176979 q = 0) : d178047 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176979, d178047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16252 q selected
    | true =>
      simp only [d176979, d178047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d176980 q = 0) : d178048 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176980, d178048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d176980, d178048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d176981 q = 0) : d178049 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176981, d178049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d176981, d178049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d176982 q = 0) : d178050 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176982, d178050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176982, d178050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d176983 q = 0) : d178051 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176983, d178051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176983, d178051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d176984 q = 0) : d178052 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176984, d178052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176984, d178052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro16254 (p : Pattern) (selected : d176985 p = 0) : d178053 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176878 q = 0) : d177971 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176878, d177971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16230 q selected
    | true =>
      simp only [d176878, d177971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176879 q = 0) : d177972 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176879, d177972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176879, d177972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176882 q = 0) : d177975 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176882, d177975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16231 q selected
    | true =>
      simp only [d176882, d177975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176883 q = 0) : d177976 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176883, d177976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176883, d177976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176884 q = 0) : d177977 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176884, d177977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176884, d177977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176885 q = 0) : d177978 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176885, d177978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176885, d177978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176911 q = 0) : d178004 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176911, d178004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176911, d178004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176985 q = 0) : d178053 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176985, d178053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176985, d178053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16255 (p : Pattern) (selected : d176986 p = 0) : d178054 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176882 q = 0) : d177975 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176882, d177975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16231 q selected
    | true =>
      simp only [d176882, d177975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176883 q = 0) : d177976 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176883, d177976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176883, d177976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176888 q = 0) : d177981 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176888, d177981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176888, d177981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176889 q = 0) : d177982 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176889, d177982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176889, d177982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176913 q = 0) : d178006 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176913, d178006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176913, d178006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176986 q = 0) : d178054 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176986, d178054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176986, d178054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16256 (p : Pattern) (selected : d176991 p = 0) : d178059 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176878 q = 0) : d177971 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176878, d177971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16230 q selected
    | true =>
      simp only [d176878, d177971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176879 q = 0) : d177972 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176879, d177972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176879, d177972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176882 q = 0) : d177975 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176882, d177975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16231 q selected
    | true =>
      simp only [d176882, d177975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176883 q = 0) : d177976 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176883, d177976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176883, d177976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176884 q = 0) : d177977 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176884, d177977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176884, d177977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176919 q = 0) : d178012 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176919, d178012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176919, d178012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176920 q = 0) : d178013 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176920, d178013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176920, d178013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176991 q = 0) : d178059 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176991, d178059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176991, d178059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16257 (p : Pattern) (selected : d176992 p = 0) : d178060 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176882 q = 0) : d177975 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176882, d177975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16231 q selected
    | true =>
      simp only [d176882, d177975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176883 q = 0) : d177976 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176883, d177976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176883, d177976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176888 q = 0) : d177981 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176888, d177981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176888, d177981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176922 q = 0) : d178015 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176922, d178015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176922, d178015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176923 q = 0) : d178016 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176923, d178016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176923, d178016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176992 q = 0) : d178060 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176992, d178060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176992, d178060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16258 (p : Pattern) (selected : d176996 p = 0) : d178064 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176934 q = 0) : d178027 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176934, d178027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16242 q selected
    | true =>
      simp only [d176934, d178027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176935 q = 0) : d178028 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176935, d178028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176935, d178028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176878 q = 0) : d177971 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176878, d177971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16230 q selected
    | true =>
      simp only [d176878, d177971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176879 q = 0) : d177972 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176879, d177972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176879, d177972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176936 q = 0) : d178029 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176936, d178029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176936, d178029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176937 q = 0) : d178030 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176937, d178030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176937, d178030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176938 q = 0) : d178031 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176938, d178031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176938, d178031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176996 q = 0) : d178064 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176996, d178064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176996, d178064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16259 (p : Pattern) (selected : d176998 p = 0) : d177993 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176951 q = 0) : d177971 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176951, d177971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16247 q selected
    | true =>
      simp only [d176951, d177971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176952 q = 0) : d177972 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176952, d177972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176952, d177972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176955 q = 0) : d177975 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176955, d177975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16248 q selected
    | true =>
      simp only [d176955, d177975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176956 q = 0) : d177976 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176956, d177976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176956, d177976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176957 q = 0) : d177977 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176957, d177977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176957, d177977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176958 q = 0) : d177978 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176958, d177978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176958, d177978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176959 q = 0) : d177979 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176959, d177979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176959, d177979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176998 q = 0) : d177993 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176998, d177993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176998, d177993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16260 (p : Pattern) (selected : d176999 p = 0) : d177994 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176955 q = 0) : d177975 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176955, d177975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16248 q selected
    | true =>
      simp only [d176955, d177975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176956 q = 0) : d177976 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176956, d177976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176956, d177976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176961 q = 0) : d177981 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176961, d177981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176961, d177981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176962 q = 0) : d177982 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176962, d177982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176962, d177982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176963 q = 0) : d177983 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176963, d177983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176963, d177983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176999 q = 0) : d177994 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176999, d177994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176999, d177994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16261 (p : Pattern) (selected : d177002 p = 0) : d178067 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176973 q = 0) : d178041 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176973, d178041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16251 q selected
    | true =>
      simp only [d176973, d178041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176974 q = 0) : d178042 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176974, d178042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176974, d178042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176975 q = 0) : d178043 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176975, d178043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176975, d178043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176976 q = 0) : d178044 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176976, d178044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176976, d178044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176977 q = 0) : d178045 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176977, d178045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176977, d178045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d177002 q = 0) : d178067 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177002, d178067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d177002, d178067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16262 (p : Pattern) (selected : d177008 p = 0) : d178073 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176915 q = 0) : d178008 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176915, d178008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16238 q selected
    | true =>
      simp only [d176915, d178008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16239 q selected
  have h2 (q : Pattern) (selected : d176916 q = 0) : d178009 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176916, d178009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176916, d178009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176917 q = 0) : d178010 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176917, d178010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176917, d178010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176918 q = 0) : d178011 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176918, d178011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176918, d178011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176925 q = 0) : d178018 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176925, d178018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16240 q selected
    | true =>
      simp only [d176925, d178018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16241 q selected
  have h6 (q : Pattern) (selected : d176926 q = 0) : d178019 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176926, d178019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176926, d178019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176927 q = 0) : d178020 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176927, d178020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176927, d178020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176940 q = 0) : d178033 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176940, d178033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16243 q selected
    | true =>
      simp only [d176940, d178033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16232 q selected
  have h9 (q : Pattern) (selected : d176965 q = 0) : d177985 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176965, d177985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16249 q selected
    | true =>
      simp only [d176965, d177985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16250 q selected
  have h10 (q : Pattern) (selected : d176966 q = 0) : d178034 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176966, d178034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d176966, d178034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d176979 q = 0) : d178047 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176979, d178047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16252 q selected
    | true =>
      simp only [d176979, d178047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d176980 q = 0) : d178048 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176980, d178048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d176980, d178048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d176981 q = 0) : d178049 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176981, d178049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d176981, d178049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d176982 q = 0) : d178050 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176982, d178050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176982, d178050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d176983 q = 0) : d178051 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176983, d178051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176983, d178051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d176987 q = 0) : d178055 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176987, d178055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16254 q selected
    | true =>
      simp only [d176987, d178055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16255 q selected
  have h17 (q : Pattern) (selected : d176988 q = 0) : d178056 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176988, d178056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176988, d178056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d176989 q = 0) : d178057 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176989, d178057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d176989, d178057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d176990 q = 0) : d178058 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176990, d178058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176990, d178058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d176993 q = 0) : d178061 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176993, d178061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16256 q selected
    | true =>
      simp only [d176993, d178061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16257 q selected
  have h21 (q : Pattern) (selected : d176994 q = 0) : d178062 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176994, d178062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176994, d178062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d176995 q = 0) : d178063 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176995, d178063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d176995, d178063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d176997 q = 0) : d178065 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176997, d178065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16258 q selected
    | true =>
      simp only [d176997, d178065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16235 q selected
  have h24 (q : Pattern) (selected : d177000 q = 0) : d177995 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177000, d177995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16259 q selected
    | true =>
      simp only [d177000, d177995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16260 q selected
  have h25 (q : Pattern) (selected : d177001 q = 0) : d178066 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177001, d178066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d177001, d178066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d177003 q = 0) : d178068 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177003, d178068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16261 q selected
    | true =>
      simp only [d177003, d178068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d177004 q = 0) : d178069 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177004, d178069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d177004, d178069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d177005 q = 0) : d178070 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177005, d178070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d177005, d178070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d177006 q = 0) : d178071 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177006, d178071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d177006, d178071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d177007 q = 0) : d178072 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177007, d178072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d177007, d178072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d177008 q = 0) : d178073 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177008, d178073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d177008, d178073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro16263 (p : Pattern) (selected : d177015 p = 0) : d178080 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176892 q = 0) : d177985 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176892, d177985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16232 q selected
    | true =>
      simp only [d176892, d177985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16233 q selected
  have h2 (q : Pattern) (selected : d176893 q = 0) : d177986 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176893, d177986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176893, d177986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176894 q = 0) : d177987 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176894, d177987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176894, d177987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176895 q = 0) : d177988 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176895, d177988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176895, d177988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176896 q = 0) : d177989 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176896, d177989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176896, d177989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d177010 q = 0) : d178075 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177010, d178075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16233 q selected
    | true =>
      simp only [d177010, d178075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d177011 q = 0) : d178076 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177011, d178076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177011, d178076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d177012 q = 0) : d178077 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177012, d178077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d177012, d178077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d177013 q = 0) : d178078 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177013, d178078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177013, d178078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d177014 q = 0) : d178079 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177014, d178079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177014, d178079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d177015 q = 0) : d178080 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177015, d178080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d177015, d178080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16264 (p : Pattern) (selected : d177021 p = 0) : d178086 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d177010 q = 0) : d178075 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177010, d178075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16233 q selected
    | true =>
      simp only [d177010, d178075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d177011 q = 0) : d178076 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177011, d178076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177011, d178076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d177012 q = 0) : d178077 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177012, d178077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d177012, d178077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d177013 q = 0) : d178078 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177013, d178078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177013, d178078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d177014 q = 0) : d178079 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177014, d178079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177014, d178079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d177016 q = 0) : d178081 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177016, d178081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16236 q selected
    | true =>
      simp only [d177016, d178081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d177017 q = 0) : d178082 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177017, d178082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177017, d178082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d177018 q = 0) : d178083 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177018, d178083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d177018, d178083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d177019 q = 0) : d178084 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177019, d178084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177019, d178084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d177020 q = 0) : d178085 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177020, d178085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177020, d178085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d177021 q = 0) : d178086 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177021, d178086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d177021, d178086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro16265 (p : Pattern) (selected : d177028 p = 0) : d178093 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176997 q = 0) : d178065 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176997, d178065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16258 q selected
    | true =>
      simp only [d176997, d178065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16235 q selected
  have h2 (q : Pattern) (selected : d177000 q = 0) : d177995 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177000, d177995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16259 q selected
    | true =>
      simp only [d177000, d177995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16260 q selected
  have h3 (q : Pattern) (selected : d177001 q = 0) : d178066 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177001, d178066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d177001, d178066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d177003 q = 0) : d178068 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177003, d178068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16261 q selected
    | true =>
      simp only [d177003, d178068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d177004 q = 0) : d178069 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177004, d178069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d177004, d178069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d177005 q = 0) : d178070 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177005, d178070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d177005, d178070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d177026 q = 0) : d178091 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177026, d178091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177026, d178091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d177027 q = 0) : d178092 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177027, d178092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177027, d178092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d177028 q = 0) : d178093 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177028, d178093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177028, d178093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16266 (p : Pattern) (selected : d177030 p = 0) : d178095 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d177016 q = 0) : d178081 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177016, d178081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16236 q selected
    | true =>
      simp only [d177016, d178081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d177017 q = 0) : d178082 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177017, d178082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177017, d178082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d177018 q = 0) : d178083 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177018, d178083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d177018, d178083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d177019 q = 0) : d178084 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177019, d178084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177019, d178084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d177020 q = 0) : d178085 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177020, d178085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177020, d178085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d177030 q = 0) : d178095 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177030, d178095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177030, d178095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16267 (p : Pattern) (selected : d13816 p = 0) : d113968 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d13813 q = 0) : d113965 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6756 q selected
  have h2 (q : Pattern) (selected : d10353 q = 0) : d101674 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6756 q selected
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13814 q = 0) : d113966 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10355 q = 0) : d101676 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d13815 q = 0) : d113967 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13815, d113967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d13815, d113967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d13816 q = 0) : d113968 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13816, d113968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d13816, d113968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16268 (p : Pattern) (selected : d15778 p = 0) : d123731 p = 1 := by
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
  have h6 (q : Pattern) (selected : d15778 q = 0) : d123731 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15778, d123731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15778, d123731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16269 (p : Pattern) (selected : d15793 p = 0) : d123746 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d15790 q = 0) : d123743 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6764 q selected
  have h2 (q : Pattern) (selected : d10412 q = 0) : d101733 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6764 q selected
    | true =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15791 q = 0) : d123744 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15791, d123744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15791, d123744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10414 q = 0) : d101735 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15792 q = 0) : d123745 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15792, d123745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15792, d123745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15793 q = 0) : d123746 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15793, d123746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15793, d123746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16270 (p : Pattern) (selected : d177048 p = 0) : d178113 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d177036 q = 0) : d178101 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177036, d178101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177036, d178101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16267 q selected
  have h2 (q : Pattern) (selected : d177037 q = 0) : d178102 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177037, d178102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177037, d178102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d177038 q = 0) : d178103 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177038, d178103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177038, d178103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d177039 q = 0) : d178104 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177039, d178104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16267 q selected
    | true =>
      simp only [d177039, d178104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16268 q selected
  have h5 (q : Pattern) (selected : d177040 q = 0) : d178105 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177040, d178105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177040, d178105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d177041 q = 0) : d178106 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177041, d178106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177041, d178106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d177042 q = 0) : d178107 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177042, d178107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d177042, d178107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d177043 q = 0) : d178108 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177043, d178108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16268 q selected
    | true =>
      simp only [d177043, d178108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16269 q selected
  have h9 (q : Pattern) (selected : d177044 q = 0) : d178109 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177044, d178109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177044, d178109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d177045 q = 0) : d178110 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177045, d178110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177045, d178110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d177046 q = 0) : d178111 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177046, d178111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d177046, d178111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d177047 q = 0) : d178112 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d177047, d178112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d177047, d178112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d177048 q = 0) : d178113 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d177048, d178113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d177048, d178113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro16271 (p : Pattern) (selected : d177053 p = 0) : d178118 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d177039 q = 0) : d178104 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177039, d178104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16267 q selected
    | true =>
      simp only [d177039, d178104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16268 q selected
  have h2 (q : Pattern) (selected : d177040 q = 0) : d178105 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177040, d178105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177040, d178105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d177041 q = 0) : d178106 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177041, d178106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177041, d178106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d177043 q = 0) : d178108 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177043, d178108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16268 q selected
    | true =>
      simp only [d177043, d178108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16269 q selected
  have h5 (q : Pattern) (selected : d177044 q = 0) : d178109 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177044, d178109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177044, d178109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d177045 q = 0) : d178110 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177045, d178110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177045, d178110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d177046 q = 0) : d178111 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177046, d178111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d177046, d178111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d177051 q = 0) : d178116 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177051, d178116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d177051, d178116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d177052 q = 0) : d178117 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d177052, d178117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d177052, d178117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d177053 q = 0) : d178118 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d177053, d178118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d177053, d178118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16272 (p : Pattern) (selected : d177059 p = 0) : d178124 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d177049 q = 0) : d178114 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177049, d178114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16270 q selected
    | true =>
      simp only [d177049, d178114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d177050 q = 0) : d178115 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177050, d178115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177050, d178115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d177054 q = 0) : d178119 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177054, d178119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16271 q selected
    | true =>
      simp only [d177054, d178119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d177055 q = 0) : d178120 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177055, d178120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177055, d178120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d177056 q = 0) : d178121 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177056, d178121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d177056, d178121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d177057 q = 0) : d178122 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177057, d178122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d177057, d178122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d177058 q = 0) : d178123 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177058, d178123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d177058, d178123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d177059 q = 0) : d178124 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177059, d178124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d177059, d178124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16273 (p : Pattern) (selected : d177061 p = 0) : d178126 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d177043 q = 0) : d178108 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177043, d178108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16268 q selected
    | true =>
      simp only [d177043, d178108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16269 q selected
  have h2 (q : Pattern) (selected : d177044 q = 0) : d178109 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177044, d178109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177044, d178109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d177045 q = 0) : d178110 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177045, d178110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177045, d178110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d177051 q = 0) : d178116 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177051, d178116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d177051, d178116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d177060 q = 0) : d178125 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d177060, d178125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d177060, d178125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d177061 q = 0) : d178126 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d177061, d178126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d177061, d178126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16274 (p : Pattern) (selected : d177067 p = 0) : d178132 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d177054 q = 0) : d178119 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177054, d178119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16271 q selected
    | true =>
      simp only [d177054, d178119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d177055 q = 0) : d178120 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177055, d178120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177055, d178120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d177062 q = 0) : d178127 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177062, d178127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16273 q selected
    | true =>
      simp only [d177062, d178127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d177063 q = 0) : d178128 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177063, d178128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177063, d178128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d177064 q = 0) : d178129 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177064, d178129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d177064, d178129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d177065 q = 0) : d178130 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177065, d178130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d177065, d178130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d177066 q = 0) : d178131 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177066, d178131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d177066, d178131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d177067 q = 0) : d178132 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177067, d178132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d177067, d178132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16275 (p : Pattern) (selected : d15831 p = 0) : d113968 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d15828 q = 0) : d113965 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15828, d113965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15828, d113965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6773 q selected
  have h2 (q : Pattern) (selected : d10468 q = 0) : d101674 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10468, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6773 q selected
    | true =>
      simp only [d10468, d101674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15829 q = 0) : d113966 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15829, d113966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15829, d113966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10470 q = 0) : d101676 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10470, d101676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10470, d101676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15830 q = 0) : d113967 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15830, d113967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15830, d113967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15831 q = 0) : d113968 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15831, d113968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15831, d113968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16276 (p : Pattern) (selected : d15838 p = 0) : d123731 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d15835 q = 0) : d123728 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15835, d123728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15835, d123728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6774 q selected
  have h2 (q : Pattern) (selected : d10482 q = 0) : d101692 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10482, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6774 q selected
    | true =>
      simp only [d10482, d101692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15836 q = 0) : d123729 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15836, d123729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15836, d123729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10484 q = 0) : d101694 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10484, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10484, d101694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15837 q = 0) : d123730 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15837, d123730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15837, d123730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15838 q = 0) : d123731 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15838, d123731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15838, d123731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16277 (p : Pattern) (selected : d15847 p = 0) : d123746 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d15844 q = 0) : d123743 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15844, d123743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15844, d123743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6779 q selected
  have h2 (q : Pattern) (selected : d10521 q = 0) : d101733 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10521, d101733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6779 q selected
    | true =>
      simp only [d10521, d101733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15845 q = 0) : d123744 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15845, d123744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15845, d123744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10523 q = 0) : d101735 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10523, d101735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10523, d101735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15846 q = 0) : d123745 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15846, d123745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15846, d123745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15847 q = 0) : d123746 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15847, d123746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15847, d123746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16278 (p : Pattern) (selected : d177078 p = 0) : d178118 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d177069 q = 0) : d178104 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177069, d178104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16275 q selected
    | true =>
      simp only [d177069, d178104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16276 q selected
  have h2 (q : Pattern) (selected : d177070 q = 0) : d178105 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177070, d178105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177070, d178105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d177071 q = 0) : d178106 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177071, d178106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177071, d178106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d177072 q = 0) : d178108 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177072, d178108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16276 q selected
    | true =>
      simp only [d177072, d178108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16277 q selected
  have h5 (q : Pattern) (selected : d177073 q = 0) : d178109 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177073, d178109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177073, d178109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d177074 q = 0) : d178110 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177074, d178110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177074, d178110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d177075 q = 0) : d178111 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177075, d178111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d177075, d178111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d177076 q = 0) : d178116 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177076, d178116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d177076, d178116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d177077 q = 0) : d178117 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d177077, d178117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d177077, d178117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d177078 q = 0) : d178118 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d177078, d178118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d177078, d178118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16279 (p : Pattern) (selected : d177082 p = 0) : d178126 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d177072 q = 0) : d178108 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177072, d178108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16276 q selected
    | true =>
      simp only [d177072, d178108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16277 q selected
  have h2 (q : Pattern) (selected : d177073 q = 0) : d178109 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177073, d178109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177073, d178109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d177074 q = 0) : d178110 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177074, d178110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177074, d178110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d177076 q = 0) : d178116 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177076, d178116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d177076, d178116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d177081 q = 0) : d178125 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d177081, d178125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d177081, d178125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d177082 q = 0) : d178126 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d177082, d178126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d177082, d178126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16280 (p : Pattern) (selected : d177088 p = 0) : d178132 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d177079 q = 0) : d178119 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177079, d178119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16278 q selected
    | true =>
      simp only [d177079, d178119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d177080 q = 0) : d178120 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177080, d178120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177080, d178120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d177083 q = 0) : d178127 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177083, d178127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16279 q selected
    | true =>
      simp only [d177083, d178127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d177084 q = 0) : d178128 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177084, d178128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177084, d178128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d177085 q = 0) : d178129 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177085, d178129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d177085, d178129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d177086 q = 0) : d178130 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177086, d178130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d177086, d178130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d177087 q = 0) : d178131 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177087, d178131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d177087, d178131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d177088 q = 0) : d178132 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177088, d178132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d177088, d178132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16281 (p : Pattern) (selected : d177092 p = 0) : d178137 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d177083 q = 0) : d178127 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177083, d178127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16279 q selected
    | true =>
      simp only [d177083, d178127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d177084 q = 0) : d178128 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177084, d178128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177084, d178128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d177089 q = 0) : d178134 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177089, d178134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d177089, d178134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d177090 q = 0) : d178135 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177090, d178135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d177090, d178135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d177091 q = 0) : d178136 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177091, d178136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d177091, d178136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d177092 q = 0) : d178137 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177092, d178137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d177092, d178137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16282 (p : Pattern) (selected : d177100 p = 0) : d178145 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d177039 q = 0) : d178104 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177039, d178104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16267 q selected
    | true =>
      simp only [d177039, d178104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16268 q selected
  have h2 (q : Pattern) (selected : d177040 q = 0) : d178105 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177040, d178105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177040, d178105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d177041 q = 0) : d178106 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177041, d178106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177041, d178106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d177043 q = 0) : d178108 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177043, d178108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16268 q selected
    | true =>
      simp only [d177043, d178108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16269 q selected
  have h5 (q : Pattern) (selected : d177044 q = 0) : d178109 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177044, d178109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177044, d178109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d177045 q = 0) : d178110 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177045, d178110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177045, d178110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d177046 q = 0) : d178111 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177046, d178111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d177046, d178111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d177095 q = 0) : d178140 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177095, d178140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16268 q selected
    | true =>
      simp only [d177095, d178140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d177096 q = 0) : d178141 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177096, d178141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177096, d178141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d177097 q = 0) : d178142 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177097, d178142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177097, d178142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d177098 q = 0) : d178143 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177098, d178143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d177098, d178143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d177099 q = 0) : d178144 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d177099, d178144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d177099, d178144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d177100 q = 0) : d178145 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d177100, d178145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d177100, d178145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro16283 (p : Pattern) (selected : d177106 p = 0) : d178151 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d177101 q = 0) : d178146 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177101, d178146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16282 q selected
    | true =>
      simp only [d177101, d178146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d177102 q = 0) : d178147 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177102, d178147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177102, d178147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d177103 q = 0) : d178148 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177103, d178148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d177103, d178148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d177104 q = 0) : d178149 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177104, d178149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d177104, d178149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d177105 q = 0) : d178150 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177105, d178150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d177105, d178150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d177106 q = 0) : d178151 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177106, d178151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d177106, d178151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16284 (p : Pattern) (selected : d177112 p = 0) : d178157 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d177068 q = 0) : d178133 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177068, d178133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16272 q selected
    | true =>
      simp only [d177068, d178133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16274 q selected
  have h2 (q : Pattern) (selected : d177093 q = 0) : d178138 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177093, d178138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16280 q selected
    | true =>
      simp only [d177093, d178138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16281 q selected
  have h3 (q : Pattern) (selected : d177094 q = 0) : d178139 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177094, d178139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d177094, d178139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d177107 q = 0) : d178152 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177107, d178152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16283 q selected
    | true =>
      simp only [d177107, d178152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d177108 q = 0) : d178153 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177108, d178153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d177108, d178153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d177109 q = 0) : d178154 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177109, d178154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d177109, d178154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d177110 q = 0) : d178155 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177110, d178155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177110, d178155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d177111 q = 0) : d178156 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177111, d178156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177111, d178156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d177112 q = 0) : d178157 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177112, d178157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177112, d178157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16285 (p : Pattern) (selected : d177117 p = 0) : d178137 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d177062 q = 0) : d178127 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177062, d178127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16273 q selected
    | true =>
      simp only [d177062, d178127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d177063 q = 0) : d178128 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177063, d178128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177063, d178128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d177114 q = 0) : d178134 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177114, d178134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d177114, d178134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d177115 q = 0) : d178135 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177115, d178135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d177115, d178135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d177116 q = 0) : d178136 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177116, d178136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d177116, d178136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d177117 q = 0) : d178137 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177117, d178137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d177117, d178137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16286 (p : Pattern) (selected : d177123 p = 0) : d178164 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d177118 q = 0) : d178159 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177118, d178159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16285 q selected
    | true =>
      simp only [d177118, d178159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d177119 q = 0) : d178160 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177119, d178160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177119, d178160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d177120 q = 0) : d178161 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177120, d178161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d177120, d178161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d177121 q = 0) : d178162 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177121, d178162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177121, d178162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d177122 q = 0) : d178163 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177122, d178163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177122, d178163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d177123 q = 0) : d178164 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177123, d178164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177123, d178164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16287 (p : Pattern) (selected : d177129 p = 0) : d178170 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d176898 q = 0) : d177991 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176898, d177991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176898, d177991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16234 q selected
  have h2 (q : Pattern) (selected : d176899 q = 0) : d177992 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d176899, d177992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176899, d177992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d176908 q = 0) : d178001 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176908, d178001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16234 q selected
    | true =>
      simp only [d176908, d178001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16237 q selected
  have h4 (q : Pattern) (selected : d176909 q = 0) : d178002 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d176909, d178002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176909, d178002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176910 q = 0) : d178003 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d176910, d178003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176910, d178003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d177009 q = 0) : d178074 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177009, d178074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16253 q selected
    | true =>
      simp only [d177009, d178074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16262 q selected
  have h7 (q : Pattern) (selected : d177022 q = 0) : d178087 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177022, d178087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16263 q selected
    | true =>
      simp only [d177022, d178087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16264 q selected
  have h8 (q : Pattern) (selected : d177023 q = 0) : d178088 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d177023, d178088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d177023, d178088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d177024 q = 0) : d178089 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d177024, d178089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d177024, d178089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d177025 q = 0) : d178090 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d177025, d178090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d177025, d178090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d177029 q = 0) : d178094 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177029, d178094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177029, d178094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16265 q selected
  have h12 (q : Pattern) (selected : d177031 q = 0) : d178096 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177031, d178096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177031, d178096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16266 q selected
  have h13 (q : Pattern) (selected : d177032 q = 0) : d178097 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d177032, d178097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d177032, d178097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d177033 q = 0) : d178098 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d177033, d178098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d177033, d178098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d177034 q = 0) : d178099 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d177034, d178099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d177034, d178099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d177035 q = 0) : d178100 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d177035, d178100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d177035, d178100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d177113 q = 0) : d178158 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177113, d178158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177113, d178158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16284 q selected
  have h18 (q : Pattern) (selected : d177124 q = 0) : d178165 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177124, d178165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177124, d178165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16286 q selected
  have h19 (q : Pattern) (selected : d177125 q = 0) : d178166 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d177125, d178166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d177125, d178166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d177126 q = 0) : d178167 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d177126, d178167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d177126, d178167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d177127 q = 0) : d178168 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d177127, d178168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d177127, d178168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d177128 q = 0) : d178169 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d177128, d178169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d177128, d178169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d177129 q = 0) : d178170 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d177129, d178170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d177129, d178170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro16288 (p : Pattern) (selected : d177135 p = 0) : d178176 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d177130 q = 0) : d178171 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d177130, d178171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177130, d178171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16287 q selected
  have h2 (q : Pattern) (selected : d177131 q = 0) : d178172 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d177131, d178172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177131, d178172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d177132 q = 0) : d178173 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d177132, d178173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177132, d178173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d177133 q = 0) : d178174 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d177133, d178174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177133, d178174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d177134 q = 0) : d178175 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d177134, d178175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177134, d178175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d177135 q = 0) : d178176 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d177135, d178176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177135, d178176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16289 (p : Pattern) (selected : d177141 p = 0) : d178182 p = 1 := by
  have h0 (q : Pattern) (selected : d176147 q = 0) : d177371 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d176147, d177371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16033 q selected
    | true =>
      simp only [d176147, d177371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16063 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d176323 q = 0) : d177520 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d176323, d177520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176323, d177520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16098 q selected
  have h3 (q : Pattern) (selected : d176324 q = 0) : d177521 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d176324, d177521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176324, d177521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176593 q = 0) : d177738 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d176593, d177738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176593, d177738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16162 q selected
  have h5 (q : Pattern) (selected : d176594 q = 0) : d177739 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d176594, d177739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176594, d177739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176595 q = 0) : d177740 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d176595, d177740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176595, d177740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176864 q = 0) : d177957 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d176864, d177957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176864, d177957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16226 q selected
  have h8 (q : Pattern) (selected : d176865 q = 0) : d177958 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d176865, d177958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176865, d177958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d176866 q = 0) : d177959 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d176866, d177959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176866, d177959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176867 q = 0) : d177960 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d176867, d177960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176867, d177960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d177136 q = 0) : d178177 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d177136, d178177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d177136, d178177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16288 q selected
  have h12 (q : Pattern) (selected : d177137 q = 0) : d178178 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d177137, d178178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d177137, d178178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d177138 q = 0) : d178179 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d177138, d178179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d177138, d178179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d177139 q = 0) : d178180 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d177139, d178180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d177139, d178180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d177140 q = 0) : d178181 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d177140, d178181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d177140, d178181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d177141 q = 0) : d178182 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d177141, d178182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d177141, d178182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro16290 (p : Pattern) (selected : d177147 p = 0) : d178188 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d177142 q = 0) : d178183 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d177142, d178183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16289 q selected
    | true =>
      simp only [d177142, d178183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d177143 q = 0) : d178184 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d177143, d178184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d177143, d178184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d177144 q = 0) : d178185 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d177144, d178185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d177144, d178185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d177145 q = 0) : d178186 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d177145, d178186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d177145, d178186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d177146 q = 0) : d178187 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d177146, d178187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d177146, d178187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d177147 q = 0) : d178188 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d177147, d178188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d177147, d178188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16291 (p : Pattern) (selected : d177153 p = 0) : d178194 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d177148 q = 0) : d178189 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d177148, d178189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16290 q selected
    | true =>
      simp only [d177148, d178189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d177149 q = 0) : d178190 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d177149, d178190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d177149, d178190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d177150 q = 0) : d178191 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d177150, d178191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d177150, d178191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d177151 q = 0) : d178192 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d177151, d178192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d177151, d178192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d177152 q = 0) : d178193 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d177152, d178193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d177152, d178193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d177153 q = 0) : d178194 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d177153, d178194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d177153, d178194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16292 (p : Pattern) (selected : d177159 p = 0) : d178200 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d177154 q = 0) : d178195 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d177154, d178195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16291 q selected
    | true =>
      simp only [d177154, d178195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d177155 q = 0) : d178196 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d177155, d178196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d177155, d178196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d177156 q = 0) : d178197 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d177156, d178197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d177156, d178197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d177157 q = 0) : d178198 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d177157, d178198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d177157, d178198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d177158 q = 0) : d178199 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d177158, d178199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d177158, d178199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d177159 q = 0) : d178200 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d177159, d178200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d177159, d178200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16293 (p : Pattern) (selected : d177165 p = 0) : d178206 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d177160 q = 0) : d178201 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d177160, d178201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16292 q selected
    | true =>
      simp only [d177160, d178201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d177161 q = 0) : d178202 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d177161, d178202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d177161, d178202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d177162 q = 0) : d178203 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d177162, d178203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d177162, d178203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d177163 q = 0) : d178204 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d177163, d178204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d177163, d178204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d177164 q = 0) : d178205 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d177164, d178205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d177164, d178205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d177165 q = 0) : d178206 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d177165, d178206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d177165, d178206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16294 (p : Pattern) (selected : d177171 p = 0) : d178212 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d177166 q = 0) : d178207 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d177166, d178207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16293 q selected
    | true =>
      simp only [d177166, d178207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d177167 q = 0) : d178208 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d177167, d178208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d177167, d178208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d177168 q = 0) : d178209 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d177168, d178209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d177168, d178209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d177169 q = 0) : d178210 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d177169, d178210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d177169, d178210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d177170 q = 0) : d178211 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d177170, d178211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d177170, d178211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d177171 q = 0) : d178212 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d177171, d178212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d177171, d178212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16295 (p : Pattern) (selected : d177177 p = 0) : d178218 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d177172 q = 0) : d178213 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d177172, d178213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16294 q selected
    | true =>
      simp only [d177172, d178213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d177173 q = 0) : d178214 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d177173, d178214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d177173, d178214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d177174 q = 0) : d178215 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d177174, d178215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d177174, d178215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d177175 q = 0) : d178216 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d177175, d178216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d177175, d178216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d177176 q = 0) : d178217 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d177176, d178217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d177176, d178217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d177177 q = 0) : d178218 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d177177, d178218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d177177, d178218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16296 (p : Pattern) (selected : d177183 p = 0) : d178224 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d177178 q = 0) : d178219 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d177178, d178219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16295 q selected
    | true =>
      simp only [d177178, d178219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d177179 q = 0) : d178220 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d177179, d178220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d177179, d178220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d177180 q = 0) : d178221 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d177180, d178221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d177180, d178221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d177181 q = 0) : d178222 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d177181, d178222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d177181, d178222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d177182 q = 0) : d178223 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d177182, d178223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d177182, d178223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d177183 q = 0) : d178224 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d177183, d178224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d177183, d178224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16297 (p : Pattern) (selected : d175949 p = 1) : d180616 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d142751 q = 1) : d142751 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d142757 q = 1) : d142757 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d175944 q = 1) : d175944 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d142783 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12661 q selected
    | true =>
      simp only [d142783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d175945 q = 1) : d180612 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d175945, d180612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d175945, d180612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142680 q = 1) : d142680 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d175946 q = 1) : d180613 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d175946, d180613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d175946, d180613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d175947 q = 1) : d180614 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d175947, d180614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d175947, d180614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d175948 q = 1) : d180615 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d175948, d180615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d175948, d180615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d175949 q = 1) : d180616 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d175949, d180616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175949, d180616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro16298 (p : Pattern) (selected : d175956 p = 1) : d180621 p = 1 := by
  have h0 (q : Pattern) (selected : d142751 q = 1) : d142751 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d142757 q = 1) : d142757 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d175944 q = 1) : d175944 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d142783 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12661 q selected
    | true =>
      simp only [d142783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d175945 q = 1) : d180612 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d175945, d180612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d175945, d180612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142680 q = 1) : d142680 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d175946 q = 1) : d180613 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d175946, d180613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d175946, d180613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d175947 q = 1) : d180614 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d175947, d180614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d175947, d180614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d175948 q = 1) : d180615 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d175948, d180615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175948, d180615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d142793 q = 1) : d142793 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d142797 q = 1) : d142797 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d175951 q = 1) : d175951 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d142801 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12663 q selected
    | true =>
      simp only [d142801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h14 (q : Pattern) (selected : d175952 q = 1) : d180617 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d175952, d180617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d175952, d180617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d142687 q = 1) : d142687 q = 1 := by
    exact selected
  have h16 (q : Pattern) (selected : d175953 q = 1) : d180618 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d175953, d180618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d175953, d180618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d175954 q = 1) : d180619 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d175954, d180619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d175954, d180619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d175955 q = 1) : d180620 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d175955, d180620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d175955, d180620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d175956 q = 1) : d180621 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d175956, d180621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d175956, d180621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro16299 (p : Pattern) (selected : d175963 p = 1) : d180628 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d175951 q = 1) : d175951 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d142801 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12663 q selected
    | true =>
      simp only [d142801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d175952 q = 1) : d180617 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d175952, d180617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d175952, d180617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d142687 q = 1) : d142687 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d175953 q = 1) : d180618 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d175953, d180618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d175953, d180618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d175961 q = 1) : d180626 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d175961, d180626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175961, d180626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d175962 q = 1) : d180627 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d175962, d180627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175962, d180627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d175963 q = 1) : d180628 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d175963, d180628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175963, d180628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16300 (p : Pattern) (selected : d175986 p = 1) : d180638 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d175981 q = 1) : d175981 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d142846 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d142846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12668 q selected
    | true =>
      simp only [d142846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d175982 q = 1) : d180634 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d175982, d180634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d175982, d180634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d142715 q = 1) : d142715 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d175983 q = 1) : d180635 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d175983, d180635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d175983, d180635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d175984 q = 1) : d180636 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d175984, d180636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175984, d180636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d175985 q = 1) : d180637 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d175985, d180637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175985, d180637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d175986 q = 1) : d180638 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d175986, d180638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175986, d180638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16301 (p : Pattern) (selected : d175992 p = 1) : d180644 p = 1 := by
  have h0 (q : Pattern) (selected : d142745 q = 1) : d142745 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d175957 q = 1) : d180622 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d175957, d180622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16297 q selected
    | true =>
      simp only [d175957, d180622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16298 q selected
  have h2 (q : Pattern) (selected : d142809 q = 1) : d142809 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d175958 q = 1) : d180623 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d175958, d180623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d175958, d180623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d175959 q = 1) : d180624 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d175959, d180624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d175959, d180624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d175960 q = 1) : d180625 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d175960, d180625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175960, d180625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d175964 q = 1) : d180629 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d175964, d180629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d175964, d180629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16299 q selected
  have h8 (q : Pattern) (selected : d175965 q = 1) : d180630 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d175965, d180630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d175965, d180630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d175966 q = 1) : d180631 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d175966, d180631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d175966, d180631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d175967 q = 1) : d180632 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d175967, d180632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d175967, d180632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d175968 q = 1) : d180633 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d175968, d180633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d175968, d180633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d175987 q = 1) : d180639 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d175987, d180639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d175987, d180639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16300 q selected
  have h13 (q : Pattern) (selected : d175988 q = 1) : d180640 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d175988, d180640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d175988, d180640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d175989 q = 1) : d180641 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d175989, d180641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d175989, d180641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d175990 q = 1) : d180642 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d175990, d180642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d175990, d180642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d175991 q = 1) : d180643 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d175991, d180643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d175991, d180643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d175992 q = 1) : d180644 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d175992, d180644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d175992, d180644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro16302 (p : Pattern) (selected : d175998 p = 1) : d180650 p = 1 := by
  have h0 (q : Pattern) (selected : d142730 q = 1) : d142730 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d175993 q = 1) : d180645 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d175993, d180645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d175993, d180645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16301 q selected
  have h3 (q : Pattern) (selected : d175994 q = 1) : d180646 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d175994, d180646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d175994, d180646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d175995 q = 1) : d180647 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d175995, d180647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d175995, d180647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d175996 q = 1) : d180648 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d175996, d180648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d175996, d180648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d175997 q = 1) : d180649 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d175997, d180649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d175997, d180649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d175998 q = 1) : d180650 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d175998, d180650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d175998, d180650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16303 (p : Pattern) (selected : d14283 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d9512 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6813 q selected
    | true =>
      simp only [d9512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9514 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d14282 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14283 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16304 (p : Pattern) (selected : d176044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176039 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16303 q selected
    | true =>
      simp only [d176039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12659 q selected
  have h2 (q : Pattern) (selected : d176040 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176041 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d142771 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d142771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12659 q selected
    | true =>
      simp only [d142771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142772 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d142772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142773 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d142773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176042 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d142774 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d142774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d142774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d176043 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176044 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d176044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16305 (p : Pattern) (selected : d176050 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176045 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16304 q selected
    | true =>
      simp only [d176045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176046 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142777 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12660 q selected
    | true =>
      simp only [d142777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142778 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176047 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176048 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176049 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176050 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16306 (p : Pattern) (selected : d176062 p = 1) : d180655 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176019 q = 1) : d176019 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d176025 q = 1) : d176025 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d176038 q = 1) : d176038 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d176051 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16305 q selected
    | true =>
      simp only [d176051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12661 q selected
  have h5 (q : Pattern) (selected : d176052 q = 1) : d180651 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176052, d180651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176052, d180651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176058 q = 1) : d176058 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d176059 q = 1) : d180652 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176059, d180652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176059, d180652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176060 q = 1) : d180653 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176060, d180653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176060, d180653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d176061 q = 1) : d180654 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176061, d180654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176061, d180654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176062 q = 1) : d180655 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176062, d180655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176062, d180655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro16307 (p : Pattern) (selected : d176074 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176045 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16304 q selected
    | true =>
      simp only [d176045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176046 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142777 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12660 q selected
    | true =>
      simp only [d142777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142778 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176047 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176048 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176049 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176074 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16308 (p : Pattern) (selected : d176083 p = 1) : d180660 p = 1 := by
  have h0 (q : Pattern) (selected : d176019 q = 1) : d176019 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176025 q = 1) : d176025 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d176038 q = 1) : d176038 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d176051 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16305 q selected
    | true =>
      simp only [d176051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12661 q selected
  have h4 (q : Pattern) (selected : d176052 q = 1) : d180651 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176052, d180651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176052, d180651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176058 q = 1) : d176058 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d176059 q = 1) : d180652 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176059, d180652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176059, d180652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176060 q = 1) : d180653 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176060, d180653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176060, d180653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176061 q = 1) : d180654 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176061, d180654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176061, d180654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d176067 q = 1) : d176067 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d176071 q = 1) : d176071 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d176073 q = 1) : d176073 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d176075 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16307 q selected
    | true =>
      simp only [d176075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12663 q selected
  have h13 (q : Pattern) (selected : d176076 q = 1) : d180656 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176076, d180656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d176076, d180656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d176079 q = 1) : d176079 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d176080 q = 1) : d180657 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176080, d180657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d176080, d180657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d176081 q = 1) : d180658 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176081, d180658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d176081, d180658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d176082 q = 1) : d180659 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176082, d180659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d176082, d180659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d176083 q = 1) : d180660 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176083, d180660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d176083, d180660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro16309 (p : Pattern) (selected : d176092 p = 1) : d180667 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176073 q = 1) : d176073 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d176075 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16307 q selected
    | true =>
      simp only [d176075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12663 q selected
  have h3 (q : Pattern) (selected : d176076 q = 1) : d180656 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176076, d180656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176076, d180656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176079 q = 1) : d176079 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d176080 q = 1) : d180657 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176080, d180657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176080, d180657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176090 q = 1) : d180665 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176090, d180665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176090, d180665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176091 q = 1) : d180666 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176091, d180666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176091, d180666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176092 q = 1) : d180667 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176092, d180667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176092, d180667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16310 (p : Pattern) (selected : d14407 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d14404 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6813 q selected
  have h2 (q : Pattern) (selected : d9512 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6813 q selected
    | true =>
      simp only [d9512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d14405 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d14405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9514 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14406 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14407 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16311 (p : Pattern) (selected : d176116 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176111 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16310 q selected
    | true =>
      simp only [d176111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12666 q selected
  have h2 (q : Pattern) (selected : d176112 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176113 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d142834 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d142834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12666 q selected
    | true =>
      simp only [d142834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d142835 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d142835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d142836 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d142836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176114 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d142837 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d142837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d142837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d176115 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176116 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d176116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16312 (p : Pattern) (selected : d176122 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176117 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16311 q selected
    | true =>
      simp only [d176117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176118 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d142840 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d142840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12667 q selected
    | true =>
      simp only [d142840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d142841 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d142841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d142841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176119 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176120 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176121 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176122 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16313 (p : Pattern) (selected : d176134 p = 1) : d180677 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176110 q = 1) : d176110 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d176123 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16312 q selected
    | true =>
      simp only [d176123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12668 q selected
  have h3 (q : Pattern) (selected : d176124 q = 1) : d180673 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176124, d180673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176124, d180673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176130 q = 1) : d176130 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d176131 q = 1) : d180674 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176131, d180674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176131, d180674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176132 q = 1) : d180675 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176132, d180675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176132, d180675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176133 q = 1) : d180676 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176133, d180676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176133, d180676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176134 q = 1) : d180677 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176134, d180677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176134, d180677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16314 (p : Pattern) (selected : d176140 p = 1) : d180683 p = 1 := by
  have h0 (q : Pattern) (selected : d176013 q = 1) : d176013 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176084 q = 1) : d180661 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176084, d180661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16306 q selected
    | true =>
      simp only [d176084, d180661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16308 q selected
  have h2 (q : Pattern) (selected : d176086 q = 1) : d176086 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d176087 q = 1) : d180662 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d176087, d180662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176087, d180662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d176088 q = 1) : d180663 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d176088, d180663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176088, d180663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176089 q = 1) : d180664 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d176089, d180664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176089, d180664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176093 q = 1) : d180668 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176093, d180668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176093, d180668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16309 q selected
  have h8 (q : Pattern) (selected : d142960 q = 1) : d142960 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d176094 q = 1) : d180669 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d176094, d180669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176094, d180669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176095 q = 1) : d180670 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d176095, d180670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d176095, d180670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d176096 q = 1) : d180671 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d176096, d180671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d176096, d180671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d176097 q = 1) : d180672 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d176097, d180672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176097, d180672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d176135 q = 1) : d180678 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176135, d180678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176135, d180678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16313 q selected
  have h14 (q : Pattern) (selected : d143008 q = 1) : d143008 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d176136 q = 1) : d180679 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d176136, d180679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d176136, d180679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d176137 q = 1) : d180680 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d176137, d180680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d176137, d180680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d176138 q = 1) : d180681 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d176138, d180681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d176138, d180681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d176139 q = 1) : d180682 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d176139, d180682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d176139, d180682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d176140 q = 1) : d180683 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d176140, d180683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d176140, d180683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro16315 (p : Pattern) (selected : d176146 p = 1) : d180689 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176141 q = 1) : d180684 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d176141, d180684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176141, d180684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16314 q selected
  have h2 (q : Pattern) (selected : d176142 q = 1) : d180685 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d176142, d180685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176142, d180685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176143 q = 1) : d180686 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d176143, d180686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176143, d180686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176144 q = 1) : d180687 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d176144, d180687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176144, d180687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176145 q = 1) : d180688 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d176145, d180688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176145, d180688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176146 q = 1) : d180689 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d176146, d180689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176146, d180689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16316 (p : Pattern) (selected : d14552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d9671 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6824 q selected
    | true =>
      simp only [d9671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9673 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d14551 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14552 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16317 (p : Pattern) (selected : d176208 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176203 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16316 q selected
    | true =>
      simp only [d176203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12686 q selected
  have h2 (q : Pattern) (selected : d176204 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176205 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143097 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12686 q selected
    | true =>
      simp only [d143097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143098 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143099 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176206 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143101 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d176207 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176208 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d176208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16318 (p : Pattern) (selected : d176214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176209 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16317 q selected
    | true =>
      simp only [d176209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176210 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143108 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12688 q selected
    | true =>
      simp only [d143108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143109 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176211 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176212 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176213 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176214 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16319 (p : Pattern) (selected : d176226 p = 1) : d180695 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176183 q = 1) : d176183 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d176189 q = 1) : d176189 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d176202 q = 1) : d176202 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d176215 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16318 q selected
    | true =>
      simp only [d176215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12690 q selected
  have h5 (q : Pattern) (selected : d176216 q = 1) : d180691 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176216, d180691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176216, d180691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176222 q = 1) : d176222 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d176223 q = 1) : d180692 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176223, d180692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176223, d180692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176224 q = 1) : d180693 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176224, d180693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176224, d180693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d176225 q = 1) : d180694 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176225, d180694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176225, d180694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176226 q = 1) : d180695 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176226, d180695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176226, d180695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro16320 (p : Pattern) (selected : d176238 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176209 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16317 q selected
    | true =>
      simp only [d176209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176210 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143108 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12688 q selected
    | true =>
      simp only [d143108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143109 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176211 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176212 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176213 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176238 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16321 (p : Pattern) (selected : d176247 p = 1) : d180700 p = 1 := by
  have h0 (q : Pattern) (selected : d176183 q = 1) : d176183 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176189 q = 1) : d176189 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d176202 q = 1) : d176202 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d176215 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16318 q selected
    | true =>
      simp only [d176215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12690 q selected
  have h4 (q : Pattern) (selected : d176216 q = 1) : d180691 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176216, d180691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176216, d180691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176222 q = 1) : d176222 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d176223 q = 1) : d180692 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176223, d180692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176223, d180692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176224 q = 1) : d180693 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176224, d180693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176224, d180693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176225 q = 1) : d180694 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176225, d180694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176225, d180694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d176231 q = 1) : d176231 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d176235 q = 1) : d176235 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d176237 q = 1) : d176237 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d176239 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16320 q selected
    | true =>
      simp only [d176239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12693 q selected
  have h13 (q : Pattern) (selected : d176240 q = 1) : d180696 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176240, d180696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d176240, d180696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d176243 q = 1) : d176243 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d176244 q = 1) : d180697 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176244, d180697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d176244, d180697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d176245 q = 1) : d180698 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176245, d180698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d176245, d180698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d176246 q = 1) : d180699 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176246, d180699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d176246, d180699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d176247 q = 1) : d180700 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176247, d180700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d176247, d180700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro16322 (p : Pattern) (selected : d176256 p = 1) : d180707 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176237 q = 1) : d176237 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d176239 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16320 q selected
    | true =>
      simp only [d176239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12693 q selected
  have h3 (q : Pattern) (selected : d176240 q = 1) : d180696 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176240, d180696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176240, d180696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176243 q = 1) : d176243 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d176244 q = 1) : d180697 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176244, d180697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176244, d180697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176254 q = 1) : d180705 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176254, d180705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176254, d180705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176255 q = 1) : d180706 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176255, d180706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176255, d180706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176256 q = 1) : d180707 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176256, d180707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176256, d180707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16323 (p : Pattern) (selected : d14692 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d14689 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6824 q selected
  have h2 (q : Pattern) (selected : d9671 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6824 q selected
    | true =>
      simp only [d9671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d14690 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d14690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9673 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d14691 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d14692 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d14692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16324 (p : Pattern) (selected : d176292 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176287 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16323 q selected
    | true =>
      simp only [d176287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12697 q selected
  have h2 (q : Pattern) (selected : d176288 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176289 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d143217 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d143217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12697 q selected
    | true =>
      simp only [d143217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d143218 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d143218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d143219 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d143219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176290 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d143221 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d143221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d143221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d176291 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176292 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d176292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16325 (p : Pattern) (selected : d176298 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176293 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16324 q selected
    | true =>
      simp only [d176293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176294 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d143228 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d143228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12699 q selected
    | true =>
      simp only [d143228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d143229 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d143229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d143229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176295 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176296 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176297 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176298 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16326 (p : Pattern) (selected : d176310 p = 1) : d180717 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176286 q = 1) : d176286 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d176299 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16325 q selected
    | true =>
      simp only [d176299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12701 q selected
  have h3 (q : Pattern) (selected : d176300 q = 1) : d180713 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176300, d180713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176300, d180713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176306 q = 1) : d176306 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d176307 q = 1) : d180714 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176307, d180714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176307, d180714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176308 q = 1) : d180715 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176308, d180715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176308, d180715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176309 q = 1) : d180716 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176309, d180716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176309, d180716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176310 q = 1) : d180717 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176310, d180717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176310, d180717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16327 (p : Pattern) (selected : d176316 p = 1) : d180723 p = 1 := by
  have h0 (q : Pattern) (selected : d176177 q = 1) : d176177 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176248 q = 1) : d180701 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176248, d180701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16319 q selected
    | true =>
      simp only [d176248, d180701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16321 q selected
  have h2 (q : Pattern) (selected : d176250 q = 1) : d176250 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d176251 q = 1) : d180702 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d176251, d180702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176251, d180702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d176252 q = 1) : d180703 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d176252, d180703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176252, d180703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176253 q = 1) : d180704 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d176253, d180704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176253, d180704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176257 q = 1) : d180708 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176257, d180708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176257, d180708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16322 q selected
  have h8 (q : Pattern) (selected : d143176 q = 1) : d143176 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d176258 q = 1) : d180709 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d176258, d180709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176258, d180709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176259 q = 1) : d180710 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d176259, d180710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d176259, d180710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d176260 q = 1) : d180711 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d176260, d180711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d176260, d180711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d176261 q = 1) : d180712 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d176261, d180712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176261, d180712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d176311 q = 1) : d180718 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176311, d180718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176311, d180718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16326 q selected
  have h14 (q : Pattern) (selected : d143261 q = 1) : d143261 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d176312 q = 1) : d180719 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d176312, d180719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d176312, d180719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d176313 q = 1) : d180720 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d176313, d180720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d176313, d180720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d176314 q = 1) : d180721 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d176314, d180721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d176314, d180721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d176315 q = 1) : d180722 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d176315, d180722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d176315, d180722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d176316 q = 1) : d180723 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d176316, d180723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d176316, d180723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro16328 (p : Pattern) (selected : d176322 p = 1) : d180729 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176317 q = 1) : d180724 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d176317, d180724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176317, d180724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16327 q selected
  have h2 (q : Pattern) (selected : d176318 q = 1) : d180725 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d176318, d180725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176318, d180725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176319 q = 1) : d180726 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d176319, d180726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176319, d180726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176320 q = 1) : d180727 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d176320, d180727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176320, d180727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176321 q = 1) : d180728 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d176321, d180728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176321, d180728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176322 q = 1) : d180729 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d176322, d180729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176322, d180729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16329 (p : Pattern) (selected : d14869 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d9908 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6838 q selected
    | true =>
      simp only [d9908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9910 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d14868 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14869 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16330 (p : Pattern) (selected : d14874 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d9918 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6839 q selected
    | true =>
      simp only [d9918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9920 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d14873 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14874 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16331 (p : Pattern) (selected : d14881 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d9952 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6843 q selected
    | true =>
      simp only [d9952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d9954 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d14880 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d14881 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d14881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16332 (p : Pattern) (selected : d176407 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176398 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16329 q selected
    | true =>
      simp only [d176398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16330 q selected
  have h2 (q : Pattern) (selected : d176399 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176400 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176401 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16330 q selected
    | true =>
      simp only [d176401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16331 q selected
  have h5 (q : Pattern) (selected : d176402 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176403 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176404 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176405 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d176406 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176407 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d176407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16333 (p : Pattern) (selected : d176411 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176401 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16330 q selected
    | true =>
      simp only [d176401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16331 q selected
  have h2 (q : Pattern) (selected : d176402 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176403 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176405 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176410 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176411 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16334 (p : Pattern) (selected : d176417 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176408 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16332 q selected
    | true =>
      simp only [d176408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176409 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176412 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16333 q selected
    | true =>
      simp only [d176412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176413 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176414 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176415 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176416 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176417 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16335 (p : Pattern) (selected : d176421 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176412 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16333 q selected
    | true =>
      simp only [d176412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176413 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176418 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176419 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176420 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176421 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16336 (p : Pattern) (selected : d176441 p = 1) : d180736 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176375 q = 1) : d176375 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d176384 q = 1) : d176384 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d176397 q = 1) : d176397 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d176422 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16334 q selected
    | true =>
      simp only [d176422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16335 q selected
  have h5 (q : Pattern) (selected : d176423 q = 1) : d180732 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176423, d180732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176423, d180732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176437 q = 1) : d176437 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d176438 q = 1) : d180733 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176438, d180733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176438, d180733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176439 q = 1) : d180734 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176439, d180734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176439, d180734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d176440 q = 1) : d180735 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176440, d180735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176440, d180735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176441 q = 1) : d180736 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176441, d180736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176441, d180736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro16337 (p : Pattern) (selected : d176455 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176408 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16332 q selected
    | true =>
      simp only [d176408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176409 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176412 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16333 q selected
    | true =>
      simp only [d176412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176413 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176414 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176415 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176416 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176455 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16338 (p : Pattern) (selected : d176456 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176412 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16333 q selected
    | true =>
      simp only [d176412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176413 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176418 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176419 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176420 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176456 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16339 (p : Pattern) (selected : d176465 p = 1) : d180741 p = 1 := by
  have h0 (q : Pattern) (selected : d176375 q = 1) : d176375 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176384 q = 1) : d176384 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d176397 q = 1) : d176397 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d176422 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16334 q selected
    | true =>
      simp only [d176422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16335 q selected
  have h4 (q : Pattern) (selected : d176423 q = 1) : d180732 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176423, d180732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176423, d180732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176437 q = 1) : d176437 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d176438 q = 1) : d180733 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176438, d180733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176438, d180733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176439 q = 1) : d180734 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176439, d180734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176439, d180734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176440 q = 1) : d180735 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176440, d180735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176440, d180735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d176447 q = 1) : d176447 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d176452 q = 1) : d176452 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d176454 q = 1) : d176454 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d176457 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16337 q selected
    | true =>
      simp only [d176457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16338 q selected
  have h13 (q : Pattern) (selected : d176458 q = 1) : d180737 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176458, d180737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d176458, d180737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d176461 q = 1) : d176461 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d176462 q = 1) : d180738 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176462, d180738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d176462, d180738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d176463 q = 1) : d180739 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176463, d180739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d176463, d180739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d176464 q = 1) : d180740 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176464, d180740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d176464, d180740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d176465 q = 1) : d180741 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176465, d180741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d176465, d180741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro16340 (p : Pattern) (selected : d176485 p = 1) : d180748 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176454 q = 1) : d176454 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d176457 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16337 q selected
    | true =>
      simp only [d176457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16338 q selected
  have h3 (q : Pattern) (selected : d176458 q = 1) : d180737 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176458, d180737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176458, d180737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176461 q = 1) : d176461 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d176462 q = 1) : d180738 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176462, d180738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176462, d180738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176483 q = 1) : d180746 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176483, d180746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176483, d180746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176484 q = 1) : d180747 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176484, d180747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176484, d180747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176485 q = 1) : d180748 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176485, d180748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176485, d180748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16341 (p : Pattern) (selected : d15060 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d15057 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6838 q selected
  have h2 (q : Pattern) (selected : d9908 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6838 q selected
    | true =>
      simp only [d9908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15058 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9910 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15059 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15060 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16342 (p : Pattern) (selected : d15067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d15064 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6839 q selected
  have h2 (q : Pattern) (selected : d9918 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6839 q selected
    | true =>
      simp only [d9918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15065 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9920 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15066 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15067 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16343 (p : Pattern) (selected : d15076 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d15073 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6843 q selected
  have h2 (q : Pattern) (selected : d9952 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6843 q selected
    | true =>
      simp only [d9952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15074 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9954 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d9954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15075 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15076 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16344 (p : Pattern) (selected : d176535 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176526 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16341 q selected
    | true =>
      simp only [d176526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16342 q selected
  have h2 (q : Pattern) (selected : d176527 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176528 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176529 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16342 q selected
    | true =>
      simp only [d176529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16343 q selected
  have h5 (q : Pattern) (selected : d176530 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176531 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176532 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176533 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d176534 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176535 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d176535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16345 (p : Pattern) (selected : d176539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176529 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16342 q selected
    | true =>
      simp only [d176529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16343 q selected
  have h2 (q : Pattern) (selected : d176530 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176531 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176533 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176538 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176539 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16346 (p : Pattern) (selected : d176545 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176536 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16344 q selected
    | true =>
      simp only [d176536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176537 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176540 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16345 q selected
    | true =>
      simp only [d176540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176541 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176542 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176543 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176544 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176545 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16347 (p : Pattern) (selected : d176549 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176540 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16345 q selected
    | true =>
      simp only [d176540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176541 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176546 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176547 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176548 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176549 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16348 (p : Pattern) (selected : d176569 p = 1) : d180758 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176525 q = 1) : d176525 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d176550 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16346 q selected
    | true =>
      simp only [d176550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16347 q selected
  have h3 (q : Pattern) (selected : d176551 q = 1) : d180754 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176551, d180754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176551, d180754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176565 q = 1) : d176565 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d176566 q = 1) : d180755 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176566, d180755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176566, d180755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176567 q = 1) : d180756 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176567, d180756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176567, d180756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176568 q = 1) : d180757 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176568, d180757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176568, d180757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176569 q = 1) : d180758 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176569, d180758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176569, d180758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16349 (p : Pattern) (selected : d176586 p = 1) : d180764 p = 1 := by
  have h0 (q : Pattern) (selected : d176367 q = 1) : d176367 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176466 q = 1) : d180742 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176466, d180742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16336 q selected
    | true =>
      simp only [d176466, d180742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16339 q selected
  have h2 (q : Pattern) (selected : d176479 q = 1) : d176479 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d176480 q = 1) : d180743 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d176480, d180743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176480, d180743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d176481 q = 1) : d180744 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d176481, d180744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176481, d180744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176482 q = 1) : d180745 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d176482, d180745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176482, d180745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176486 q = 1) : d180749 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176486, d180749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176486, d180749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16340 q selected
  have h8 (q : Pattern) (selected : d176488 q = 1) : d176488 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d176489 q = 1) : d180750 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d176489, d180750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176489, d180750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176490 q = 1) : d180751 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d176490, d180751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d176490, d180751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d176491 q = 1) : d180752 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d176491, d180752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d176491, d180752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d176492 q = 1) : d180753 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d176492, d180753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176492, d180753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d176570 q = 1) : d180759 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176570, d180759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176570, d180759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16348 q selected
  have h14 (q : Pattern) (selected : d176581 q = 1) : d176581 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d176582 q = 1) : d180760 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d176582, d180760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d176582, d180760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d176583 q = 1) : d180761 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d176583, d180761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d176583, d180761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d176584 q = 1) : d180762 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d176584, d180762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d176584, d180762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d176585 q = 1) : d180763 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d176585, d180763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d176585, d180763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d176586 q = 1) : d180764 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d176586, d180764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d176586, d180764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro16350 (p : Pattern) (selected : d176592 p = 1) : d180770 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176587 q = 1) : d180765 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d176587, d180765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176587, d180765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16349 q selected
  have h2 (q : Pattern) (selected : d176588 q = 1) : d180766 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d176588, d180766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176588, d180766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176589 q = 1) : d180767 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d176589, d180767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176589, d180767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176590 q = 1) : d180768 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d176590, d180768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176590, d180768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176591 q = 1) : d180769 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d176591, d180769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176591, d180769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176592 q = 1) : d180770 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d176592, d180770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176592, d180770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16351 (p : Pattern) (selected : d15262 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10200 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6856 q selected
    | true =>
      simp only [d10200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10202 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15261 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15262 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16352 (p : Pattern) (selected : d15267 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10215 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6857 q selected
    | true =>
      simp only [d10215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10217 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15266 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15267 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16353 (p : Pattern) (selected : d15274 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10255 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6862 q selected
    | true =>
      simp only [d10255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10257 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15273 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15274 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16354 (p : Pattern) (selected : d176678 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176669 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16351 q selected
    | true =>
      simp only [d176669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16352 q selected
  have h2 (q : Pattern) (selected : d176670 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176671 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176672 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16352 q selected
    | true =>
      simp only [d176672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16353 q selected
  have h5 (q : Pattern) (selected : d176673 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176674 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176675 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176676 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d176677 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176678 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d176678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16355 (p : Pattern) (selected : d176682 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176672 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16352 q selected
    | true =>
      simp only [d176672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16353 q selected
  have h2 (q : Pattern) (selected : d176673 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176674 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176676 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176681 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176682 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16356 (p : Pattern) (selected : d176688 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176679 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16354 q selected
    | true =>
      simp only [d176679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176680 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176683 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16355 q selected
    | true =>
      simp only [d176683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176685 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176686 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176687 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176688 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16357 (p : Pattern) (selected : d176692 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176683 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16355 q selected
    | true =>
      simp only [d176683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176689 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176690 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176691 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176692 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16358 (p : Pattern) (selected : d176712 p = 1) : d180778 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176646 q = 1) : d176646 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d176655 q = 1) : d176655 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d176668 q = 1) : d176668 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d176693 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16356 q selected
    | true =>
      simp only [d176693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16357 q selected
  have h5 (q : Pattern) (selected : d176694 q = 1) : d180774 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176694, d180774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176694, d180774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176708 q = 1) : d176708 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d176709 q = 1) : d180775 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176709, d180775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176709, d180775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176710 q = 1) : d180776 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176710, d180776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176710, d180776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d176711 q = 1) : d180777 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176711, d180777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176711, d180777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176712 q = 1) : d180778 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176712, d180778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176712, d180778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro16359 (p : Pattern) (selected : d176726 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176679 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16354 q selected
    | true =>
      simp only [d176679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176680 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176683 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16355 q selected
    | true =>
      simp only [d176683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176685 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176686 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176687 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176726 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16360 (p : Pattern) (selected : d176727 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176683 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16355 q selected
    | true =>
      simp only [d176683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176684 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176689 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176690 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176691 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176727 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16361 (p : Pattern) (selected : d176736 p = 1) : d180783 p = 1 := by
  have h0 (q : Pattern) (selected : d176646 q = 1) : d176646 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176655 q = 1) : d176655 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d176668 q = 1) : d176668 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d176693 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16356 q selected
    | true =>
      simp only [d176693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16357 q selected
  have h4 (q : Pattern) (selected : d176694 q = 1) : d180774 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176694, d180774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176694, d180774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176708 q = 1) : d176708 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d176709 q = 1) : d180775 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176709, d180775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176709, d180775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176710 q = 1) : d180776 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176710, d180776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176710, d180776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176711 q = 1) : d180777 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176711, d180777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176711, d180777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d176718 q = 1) : d176718 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d176723 q = 1) : d176723 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d176725 q = 1) : d176725 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d176728 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16359 q selected
    | true =>
      simp only [d176728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16360 q selected
  have h13 (q : Pattern) (selected : d176729 q = 1) : d180779 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176729, d180779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d176729, d180779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d176732 q = 1) : d176732 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d176733 q = 1) : d180780 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176733, d180780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d176733, d180780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d176734 q = 1) : d180781 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176734, d180781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d176734, d180781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d176735 q = 1) : d180782 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176735, d180782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d176735, d180782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d176736 q = 1) : d180783 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176736, d180783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d176736, d180783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro16362 (p : Pattern) (selected : d176756 p = 1) : d180790 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176725 q = 1) : d176725 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d176728 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16359 q selected
    | true =>
      simp only [d176728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16360 q selected
  have h3 (q : Pattern) (selected : d176729 q = 1) : d180779 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176729, d180779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176729, d180779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176732 q = 1) : d176732 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d176733 q = 1) : d180780 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176733, d180780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176733, d180780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176754 q = 1) : d180788 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176754, d180788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176754, d180788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176755 q = 1) : d180789 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176755, d180789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176755, d180789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176756 q = 1) : d180790 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176756, d180790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176756, d180790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16363 (p : Pattern) (selected : d15453 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d15450 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6856 q selected
  have h2 (q : Pattern) (selected : d10200 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6856 q selected
    | true =>
      simp only [d10200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15451 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10202 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15452 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15453 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16364 (p : Pattern) (selected : d15460 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d15457 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6857 q selected
  have h2 (q : Pattern) (selected : d10215 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6857 q selected
    | true =>
      simp only [d10215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15458 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10217 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15459 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15460 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16365 (p : Pattern) (selected : d15469 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d15466 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6862 q selected
  have h2 (q : Pattern) (selected : d10255 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6862 q selected
    | true =>
      simp only [d10255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15467 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10257 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15468 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15469 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16366 (p : Pattern) (selected : d176806 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176797 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16363 q selected
    | true =>
      simp only [d176797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16364 q selected
  have h2 (q : Pattern) (selected : d176798 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176799 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176800 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16364 q selected
    | true =>
      simp only [d176800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16365 q selected
  have h5 (q : Pattern) (selected : d176801 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176802 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176803 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176804 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d176805 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176806 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d176806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16367 (p : Pattern) (selected : d176810 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176800 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16364 q selected
    | true =>
      simp only [d176800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16365 q selected
  have h2 (q : Pattern) (selected : d176801 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176802 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176804 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176809 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176810 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16368 (p : Pattern) (selected : d176816 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176807 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16366 q selected
    | true =>
      simp only [d176807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176808 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176811 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16367 q selected
    | true =>
      simp only [d176811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176812 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176813 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176814 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176815 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176816 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16369 (p : Pattern) (selected : d176820 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176811 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16367 q selected
    | true =>
      simp only [d176811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176812 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176817 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176818 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176819 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176820 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16370 (p : Pattern) (selected : d176840 p = 1) : d180800 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176796 q = 1) : d176796 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d176821 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16368 q selected
    | true =>
      simp only [d176821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16369 q selected
  have h3 (q : Pattern) (selected : d176822 q = 1) : d180796 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176822, d180796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176822, d180796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176836 q = 1) : d176836 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d176837 q = 1) : d180797 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176837, d180797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176837, d180797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176838 q = 1) : d180798 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176838, d180798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176838, d180798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176839 q = 1) : d180799 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176839, d180799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176839, d180799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176840 q = 1) : d180800 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176840, d180800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176840, d180800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16371 (p : Pattern) (selected : d176857 p = 1) : d180806 p = 1 := by
  have h0 (q : Pattern) (selected : d176638 q = 1) : d176638 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176737 q = 1) : d180784 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176737, d180784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16358 q selected
    | true =>
      simp only [d176737, d180784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16361 q selected
  have h2 (q : Pattern) (selected : d176750 q = 1) : d176750 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d176751 q = 1) : d180785 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d176751, d180785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176751, d180785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d176752 q = 1) : d180786 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d176752, d180786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176752, d180786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176753 q = 1) : d180787 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d176753, d180787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176753, d180787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176757 q = 1) : d180791 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176757, d180791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176757, d180791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16362 q selected
  have h8 (q : Pattern) (selected : d176759 q = 1) : d176759 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d176760 q = 1) : d180792 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d176760, d180792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176760, d180792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176761 q = 1) : d180793 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d176761, d180793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d176761, d180793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d176762 q = 1) : d180794 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d176762, d180794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d176762, d180794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d176763 q = 1) : d180795 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d176763, d180795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176763, d180795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d176841 q = 1) : d180801 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d176841, d180801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176841, d180801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16370 q selected
  have h14 (q : Pattern) (selected : d176852 q = 1) : d176852 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d176853 q = 1) : d180802 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d176853, d180802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d176853, d180802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d176854 q = 1) : d180803 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d176854, d180803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d176854, d180803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d176855 q = 1) : d180804 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d176855, d180804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d176855, d180804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d176856 q = 1) : d180805 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d176856, d180805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d176856, d180805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d176857 q = 1) : d180806 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d176857, d180806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d176857, d180806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro16372 (p : Pattern) (selected : d176863 p = 1) : d180812 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176858 q = 1) : d180807 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d176858, d180807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176858, d180807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16371 q selected
  have h2 (q : Pattern) (selected : d176859 q = 1) : d180808 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d176859, d180808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176859, d180808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176860 q = 1) : d180809 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d176860, d180809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176860, d180809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176861 q = 1) : d180810 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d176861, d180810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176861, d180810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176862 q = 1) : d180811 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d176862, d180811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176862, d180811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176863 q = 1) : d180812 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d176863, d180812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176863, d180812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16373 (p : Pattern) (selected : d15650 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10468 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6873 q selected
    | true =>
      simp only [d10468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10470 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15649 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15650 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16374 (p : Pattern) (selected : d15655 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10482 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6874 q selected
    | true =>
      simp only [d10482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10484 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15654 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15655 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16375 (p : Pattern) (selected : d15662 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10521 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6879 q selected
    | true =>
      simp only [d10521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10523 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15661 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d15662 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro16376 (p : Pattern) (selected : d176950 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176941 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16373 q selected
    | true =>
      simp only [d176941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16374 q selected
  have h2 (q : Pattern) (selected : d176942 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176943 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176944 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16374 q selected
    | true =>
      simp only [d176944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16375 q selected
  have h5 (q : Pattern) (selected : d176945 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176946 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176947 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176948 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d176949 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176950 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d176950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16377 (p : Pattern) (selected : d176954 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176944 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16374 q selected
    | true =>
      simp only [d176944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16375 q selected
  have h2 (q : Pattern) (selected : d176945 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d176945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176946 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d176946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176948 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d176948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176953 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d176953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176954 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d176954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16378 (p : Pattern) (selected : d176960 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176951 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16376 q selected
    | true =>
      simp only [d176951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176952 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176955 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16377 q selected
    | true =>
      simp only [d176955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176956 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176957 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176958 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176959 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176960 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16379 (p : Pattern) (selected : d176964 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176955 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16377 q selected
    | true =>
      simp only [d176955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176956 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176961 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176962 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176963 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176964 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16380 (p : Pattern) (selected : d176984 p = 1) : d180821 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176918 q = 1) : d176918 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d176927 q = 1) : d176927 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d176940 q = 1) : d176940 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d176965 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16378 q selected
    | true =>
      simp only [d176965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16379 q selected
  have h5 (q : Pattern) (selected : d176966 q = 1) : d180817 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176966, d180817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176966, d180817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176980 q = 1) : d176980 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d176981 q = 1) : d180818 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176981, d180818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176981, d180818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176982 q = 1) : d180819 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176982, d180819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176982, d180819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d176983 q = 1) : d180820 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176983, d180820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176983, d180820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176984 q = 1) : d180821 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d176984, d180821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176984, d180821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro16381 (p : Pattern) (selected : d176998 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176951 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16376 q selected
    | true =>
      simp only [d176951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176952 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176955 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16377 q selected
    | true =>
      simp only [d176955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176956 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176957 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176958 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d176959 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d176998 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d176998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16382 (p : Pattern) (selected : d176999 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176955 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d176955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16377 q selected
    | true =>
      simp only [d176955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d176956 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d176956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d176961 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d176961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d176962 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d176962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d176963 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d176963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d176999 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d176999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d176999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16383 (p : Pattern) (selected : d177008 p = 1) : d180826 p = 1 := by
  have h0 (q : Pattern) (selected : d176918 q = 1) : d176918 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176927 q = 1) : d176927 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d176940 q = 1) : d176940 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d176965 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d176965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16378 q selected
    | true =>
      simp only [d176965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16379 q selected
  have h4 (q : Pattern) (selected : d176966 q = 1) : d180817 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d176966, d180817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d176966, d180817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d176980 q = 1) : d176980 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d176981 q = 1) : d180818 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d176981, d180818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d176981, d180818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176982 q = 1) : d180819 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d176982, d180819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176982, d180819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d176983 q = 1) : d180820 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d176983, d180820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176983, d180820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d176990 q = 1) : d176990 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d176995 q = 1) : d176995 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d176997 q = 1) : d176997 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d177000 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16381 q selected
    | true =>
      simp only [d177000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16382 q selected
  have h13 (q : Pattern) (selected : d177001 q = 1) : d180822 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177001, d180822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d177001, d180822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d177004 q = 1) : d177004 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d177005 q = 1) : d180823 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177005, d180823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d177005, d180823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d177006 q = 1) : d180824 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177006, d180824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d177006, d180824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d177007 q = 1) : d180825 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177007, d180825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d177007, d180825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d177008 q = 1) : d180826 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177008, d180826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d177008, d180826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro16384 (p : Pattern) (selected : d177028 p = 1) : d180833 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176997 q = 1) : d176997 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d177000 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16381 q selected
    | true =>
      simp only [d177000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16382 q selected
  have h3 (q : Pattern) (selected : d177001 q = 1) : d180822 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177001, d180822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d177001, d180822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d177004 q = 1) : d177004 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d177005 q = 1) : d180823 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177005, d180823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d177005, d180823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d177026 q = 1) : d180831 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177026, d180831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177026, d180831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d177027 q = 1) : d180832 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177027, d180832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177027, d180832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d177028 q = 1) : d180833 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177028, d180833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177028, d180833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16385 (p : Pattern) (selected : d15831 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d15828 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6873 q selected
  have h2 (q : Pattern) (selected : d10468 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6873 q selected
    | true =>
      simp only [d10468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15829 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10470 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15830 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15831 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16386 (p : Pattern) (selected : d15838 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d15835 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6874 q selected
  have h2 (q : Pattern) (selected : d10482 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6874 q selected
    | true =>
      simp only [d10482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15836 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10484 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15837 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15838 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16387 (p : Pattern) (selected : d15847 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d15844 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6879 q selected
  have h2 (q : Pattern) (selected : d10521 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6879 q selected
    | true =>
      simp only [d10521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d15845 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d15845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10523 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d15846 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d15846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d15847 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d15847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16388 (p : Pattern) (selected : d177078 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d177069 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16385 q selected
    | true =>
      simp only [d177069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16386 q selected
  have h2 (q : Pattern) (selected : d177070 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d177071 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d177072 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16386 q selected
    | true =>
      simp only [d177072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16387 q selected
  have h5 (q : Pattern) (selected : d177073 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d177074 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d177075 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d177075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d177076 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d177076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d177077 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d177077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d177077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d177078 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d177078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d177078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16389 (p : Pattern) (selected : d177082 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d177072 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d177072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16386 q selected
    | true =>
      simp only [d177072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16387 q selected
  have h2 (q : Pattern) (selected : d177073 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d177074 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d177074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d177076 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d177076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d177076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d177081 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d177081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d177081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d177082 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d177082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d177082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16390 (p : Pattern) (selected : d177088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d177079 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16388 q selected
    | true =>
      simp only [d177079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d177080 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d177083 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16389 q selected
    | true =>
      simp only [d177083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d177084 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d177085 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d177085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d177086 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d177086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d177087 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d177087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d177088 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d177088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16391 (p : Pattern) (selected : d177092 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d177083 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d177083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16389 q selected
    | true =>
      simp only [d177083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d177084 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d177084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d177089 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d177089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d177089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d177090 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d177090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d177090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d177091 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d177091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d177091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d177092 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d177092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d177092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16392 (p : Pattern) (selected : d177112 p = 1) : d180843 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d177068 q = 1) : d177068 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d177093 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d177093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16390 q selected
    | true =>
      simp only [d177093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16391 q selected
  have h3 (q : Pattern) (selected : d177094 q = 1) : d180839 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d177094, d180839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d177094, d180839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d177108 q = 1) : d177108 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d177109 q = 1) : d180840 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d177109, d180840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d177109, d180840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d177110 q = 1) : d180841 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d177110, d180841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177110, d180841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d177111 q = 1) : d180842 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d177111, d180842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177111, d180842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d177112 q = 1) : d180843 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d177112, d180843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177112, d180843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro16393 (p : Pattern) (selected : d177129 p = 1) : d180849 p = 1 := by
  have h0 (q : Pattern) (selected : d176910 q = 1) : d176910 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d177009 q = 1) : d180827 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177009, d180827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16380 q selected
    | true =>
      simp only [d177009, d180827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16383 q selected
  have h2 (q : Pattern) (selected : d177022 q = 1) : d177022 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d177023 q = 1) : d180828 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d177023, d180828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d177023, d180828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d177024 q = 1) : d180829 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d177024, d180829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d177024, d180829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d177025 q = 1) : d180830 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d177025, d180830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177025, d180830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d177029 q = 1) : d180834 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177029, d180834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d177029, d180834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16384 q selected
  have h8 (q : Pattern) (selected : d177031 q = 1) : d177031 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d177032 q = 1) : d180835 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d177032, d180835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d177032, d180835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d177033 q = 1) : d180836 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d177033, d180836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d177033, d180836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d177034 q = 1) : d180837 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d177034, d180837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d177034, d180837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d177035 q = 1) : d180838 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d177035, d180838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d177035, d180838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d177113 q = 1) : d180844 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d177113, d180844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d177113, d180844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16392 q selected
  have h14 (q : Pattern) (selected : d177124 q = 1) : d177124 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d177125 q = 1) : d180845 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d177125, d180845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d177125, d180845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d177126 q = 1) : d180846 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d177126, d180846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d177126, d180846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d177127 q = 1) : d180847 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d177127, d180847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d177127, d180847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d177128 q = 1) : d180848 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d177128, d180848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d177128, d180848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d177129 q = 1) : d180849 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d177129, d180849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d177129, d180849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro16394 (p : Pattern) (selected : d177135 p = 1) : d180855 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d177130 q = 1) : d180850 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d177130, d180850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177130, d180850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16393 q selected
  have h2 (q : Pattern) (selected : d177131 q = 1) : d180851 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d177131, d180851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177131, d180851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d177132 q = 1) : d180852 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d177132, d180852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177132, d180852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d177133 q = 1) : d180853 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d177133, d180853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177133, d180853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d177134 q = 1) : d180854 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d177134, d180854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177134, d180854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d177135 q = 1) : d180855 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d177135, d180855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177135, d180855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16395 (p : Pattern) (selected : d177141 p = 1) : d180861 p = 1 := by
  have h0 (q : Pattern) (selected : d176147 q = 1) : d180690 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d176147, d180690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16302 q selected
    | true =>
      simp only [d176147, d180690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16315 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d176323 q = 1) : d180730 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d176323, d180730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176323, d180730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16328 q selected
  have h3 (q : Pattern) (selected : d176324 q = 1) : d180731 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d176324, d180731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d176324, d180731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176593 q = 1) : d180771 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d176593, d180771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176593, d180771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16350 q selected
  have h5 (q : Pattern) (selected : d176594 q = 1) : d180772 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d176594, d180772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176594, d180772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d176595 q = 1) : d180773 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d176595, d180773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d176595, d180773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d176864 q = 1) : d180813 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d176864, d180813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176864, d180813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16372 q selected
  have h8 (q : Pattern) (selected : d176865 q = 1) : d180814 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d176865, d180814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176865, d180814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d176866 q = 1) : d180815 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d176866, d180815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d176866, d180815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d176867 q = 1) : d180816 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d176867, d180816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d176867, d180816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d177136 q = 1) : d180856 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d177136, d180856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d177136, d180856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16394 q selected
  have h12 (q : Pattern) (selected : d177137 q = 1) : d180857 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d177137, d180857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d177137, d180857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d177138 q = 1) : d180858 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d177138, d180858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d177138, d180858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d177139 q = 1) : d180859 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d177139, d180859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d177139, d180859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d177140 q = 1) : d180860 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d177140, d180860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d177140, d180860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d177141 q = 1) : d180861 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d177141, d180861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d177141, d180861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro16396 (p : Pattern) (selected : d177147 p = 1) : d180867 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d177142 q = 1) : d180862 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d177142, d180862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16395 q selected
    | true =>
      simp only [d177142, d180862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d177143 q = 1) : d180863 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d177143, d180863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d177143, d180863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d177144 q = 1) : d180864 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d177144, d180864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d177144, d180864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d177145 q = 1) : d180865 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d177145, d180865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d177145, d180865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d177146 q = 1) : d180866 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d177146, d180866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d177146, d180866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d177147 q = 1) : d180867 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d177147, d180867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d177147, d180867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16397 (p : Pattern) (selected : d177153 p = 1) : d180873 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d177148 q = 1) : d180868 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d177148, d180868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16396 q selected
    | true =>
      simp only [d177148, d180868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d177149 q = 1) : d180869 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d177149, d180869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d177149, d180869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d177150 q = 1) : d180870 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d177150, d180870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d177150, d180870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d177151 q = 1) : d180871 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d177151, d180871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d177151, d180871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d177152 q = 1) : d180872 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d177152, d180872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d177152, d180872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d177153 q = 1) : d180873 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d177153, d180873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d177153, d180873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16398 (p : Pattern) (selected : d177159 p = 1) : d180879 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d177154 q = 1) : d180874 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d177154, d180874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16397 q selected
    | true =>
      simp only [d177154, d180874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d177155 q = 1) : d180875 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d177155, d180875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d177155, d180875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d177156 q = 1) : d180876 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d177156, d180876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d177156, d180876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d177157 q = 1) : d180877 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d177157, d180877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d177157, d180877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d177158 q = 1) : d180878 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d177158, d180878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d177158, d180878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d177159 q = 1) : d180879 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d177159, d180879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d177159, d180879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16399 (p : Pattern) (selected : d177165 p = 1) : d180885 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d177160 q = 1) : d180880 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d177160, d180880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16398 q selected
    | true =>
      simp only [d177160, d180880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d177161 q = 1) : d180881 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d177161, d180881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d177161, d180881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d177162 q = 1) : d180882 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d177162, d180882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d177162, d180882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d177163 q = 1) : d180883 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d177163, d180883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d177163, d180883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d177164 q = 1) : d180884 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d177164, d180884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d177164, d180884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d177165 q = 1) : d180885 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d177165, d180885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d177165, d180885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16400 (p : Pattern) (selected : d177171 p = 1) : d180891 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d177166 q = 1) : d180886 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d177166, d180886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16399 q selected
    | true =>
      simp only [d177166, d180886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d177167 q = 1) : d180887 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d177167, d180887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d177167, d180887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d177168 q = 1) : d180888 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d177168, d180888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d177168, d180888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d177169 q = 1) : d180889 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d177169, d180889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d177169, d180889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d177170 q = 1) : d180890 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d177170, d180890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d177170, d180890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d177171 q = 1) : d180891 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d177171, d180891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d177171, d180891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16401 (p : Pattern) (selected : d177177 p = 1) : d180897 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d177172 q = 1) : d180892 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d177172, d180892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16400 q selected
    | true =>
      simp only [d177172, d180892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d177173 q = 1) : d180893 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d177173, d180893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d177173, d180893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d177174 q = 1) : d180894 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d177174, d180894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d177174, d180894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d177175 q = 1) : d180895 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d177175, d180895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d177175, d180895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d177176 q = 1) : d180896 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d177176, d180896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d177176, d180896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d177177 q = 1) : d180897 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d177177, d180897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d177177, d180897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16402 (p : Pattern) (selected : d177183 p = 1) : d180903 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d177178 q = 1) : d180898 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d177178, d180898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16401 q selected
    | true =>
      simp only [d177178, d180898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d177179 q = 1) : d180899 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d177179, d180899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d177179, d180899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d177180 q = 1) : d180900 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d177180, d180900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d177180, d180900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d177181 q = 1) : d180901 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d177181, d180901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d177181, d180901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d177182 q = 1) : d180902 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d177182, d180902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d177182, d180902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d177183 q = 1) : d180903 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d177183, d180903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d177183, d180903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16403 (p : Pattern) (selected : d17564 p = 2) : d0 p = 1 := by
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
  have h2 (q : Pattern) (selected : d25 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro645 q selected
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d67 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17561 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17562 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17563 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d17564 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro16404 (p : Pattern) (selected : d17570 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17565 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16403 q selected
    | true =>
      simp only [d17565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d17566 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17567 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17568 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17569 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17570 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16405 (p : Pattern) (selected : d17576 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17571 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16404 q selected
    | true =>
      simp only [d17571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d17572 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17573 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d17573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d17574 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17575 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17576 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16406 (p : Pattern) (selected : d17582 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17577 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16405 q selected
    | true =>
      simp only [d17577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d17578 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d17578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d17579 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d17579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d17580 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d17581 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17582 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16407 (p : Pattern) (selected : d17588 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17583 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16406 q selected
  have h2 (q : Pattern) (selected : d17584 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d17584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d17584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d17585 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d17585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d17585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d17586 q = 2) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d17586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17587 q = 2) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d17587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17588 q = 2) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d17588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16408 (p : Pattern) (selected : d17596 p = 2) : d0 p = 1 := by
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
  have h2 (q : Pattern) (selected : d139 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro663 q selected
    | true =>
      simp only [d139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d227 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17593 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17594 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d66 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro645 q selected
  have h7 (q : Pattern) (selected : d25 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro645 q selected
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d67 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d17561 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d17561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d17562 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d17562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d17595 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d17563 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d17563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d17596 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d17596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro16409 (p : Pattern) (selected : d17602 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17597 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16408 q selected
    | true =>
      simp only [d17597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16403 q selected
  have h2 (q : Pattern) (selected : d17598 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17599 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17565 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16403 q selected
    | true =>
      simp only [d17565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17566 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17567 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d17600 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d17568 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d17601 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d17601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d17602 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d17602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16410 (p : Pattern) (selected : d17608 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17603 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16409 q selected
    | true =>
      simp only [d17603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d17604 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17571 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16404 q selected
    | true =>
      simp only [d17571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d17572 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d17605 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d17605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17606 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d17607 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d17608 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d17608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16411 (p : Pattern) (selected : d17613 p = 2) : d17564 p = 1 := by
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
  have h2 (q : Pattern) (selected : d170 q = 2) : d25 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, d25, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro668 q selected
    | true =>
      simp only [d170, d25, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246 q = 2) : d67 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246, d67, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246, d67, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17610 q = 2) : d17561 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17610, d17561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17610, d17561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17611 q = 2) : d17562 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17611, d17562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17611, d17562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17612 q = 2) : d17563 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17612, d17563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17612, d17563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d17613 q = 2) : d17564 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17613, d17564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17613, d17564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro16412 (p : Pattern) (selected : d17619 p = 2) : d17570 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17614 q = 2) : d17565 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17614, d17565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16411 q selected
    | true =>
      simp only [d17614, d17565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d17615 q = 2) : d17566 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17615, d17566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17615, d17566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17616 q = 2) : d17567 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17616, d17567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17616, d17567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17617 q = 2) : d17568 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17617, d17568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17617, d17568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17618 q = 2) : d17569 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17618, d17569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17618, d17569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17619 q = 2) : d17570 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17619, d17570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17619, d17570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16413 (p : Pattern) (selected : d17625 p = 2) : d17576 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17620 q = 2) : d17571 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17620, d17571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16412 q selected
    | true =>
      simp only [d17620, d17571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d17621 q = 2) : d17572 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17621, d17572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17621, d17572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17622 q = 2) : d17573 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17622, d17573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d17622, d17573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d17623 q = 2) : d17574 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17623, d17574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17623, d17574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17624 q = 2) : d17575 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17624, d17575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17624, d17575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17625 q = 2) : d17576 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17625, d17576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17625, d17576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16414 (p : Pattern) (selected : d17631 p = 2) : d17696 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17609 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16410 q selected
    | true =>
      simp only [d17609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16405 q selected
  have h2 (q : Pattern) (selected : d17626 q = 2) : d17577 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17626, d17577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16413 q selected
    | true =>
      simp only [d17626, d17577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d17627 q = 2) : d17692 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17627, d17692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d17627, d17692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17577 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16405 q selected
    | true =>
      simp only [d17577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17578 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17628 q = 2) : d17693 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17628, d17693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17628, d17693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d17629 q = 2) : d17694 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17629, d17694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17629, d17694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d17630 q = 2) : d17695 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17630, d17695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17630, d17695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d17631 q = 2) : d17696 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17631, d17696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17631, d17696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16415 (p : Pattern) (selected : d17637 p = 2) : d61083 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17632 q = 2) : d17697 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17632, d17697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17632, d17697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16414 q selected
  have h2 (q : Pattern) (selected : d17633 q = 2) : d61079 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d17633, d61079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d17633, d61079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d17634 q = 2) : d61080 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d17634, d61080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d17634, d61080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d17635 q = 2) : d61081 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d17635, d61081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17635, d61081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17636 q = 2) : d61082 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d17636, d61082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17636, d61082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17637 q = 2) : d61083 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d17637, d61083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17637, d61083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16416 (p : Pattern) (selected : d17649 p = 2) : d0 p = 1 := by
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
  have h2 (q : Pattern) (selected : d319 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro693 q selected
    | true =>
      simp only [d319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d413 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17643 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17644 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d226 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro663 q selected
  have h7 (q : Pattern) (selected : d139 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro663 q selected
    | true =>
      simp only [d139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d227 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d17593 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d17593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d17594 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d17594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d17645 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d12599 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10492 q selected
  have h13 (q : Pattern) (selected : d9382 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10492 q selected
    | true =>
      simp only [d9382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d12600 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d12600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d17646 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d17646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d17647 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d17647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d66 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro645 q selected
  have h18 (q : Pattern) (selected : d25 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro645 q selected
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d67 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d17561 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d17561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d17562 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d17562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d17648 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d17648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d17649 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d17649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro16417 (p : Pattern) (selected : d17655 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17650 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16416 q selected
    | true =>
      simp only [d17650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16408 q selected
  have h2 (q : Pattern) (selected : d17651 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17652 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17597 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16408 q selected
    | true =>
      simp only [d17597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16403 q selected
  have h5 (q : Pattern) (selected : d17598 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17599 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d17653 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d17565 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16403 q selected
    | true =>
      simp only [d17565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d17566 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d17567 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d17600 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d17654 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d17654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d17655 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d17655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro16418 (p : Pattern) (selected : d17661 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17656 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16417 q selected
    | true =>
      simp only [d17656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d17657 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17603 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16409 q selected
    | true =>
      simp only [d17603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d17604 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d17658 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d17658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17659 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d17660 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d17661 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d17661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16419 (p : Pattern) (selected : d17666 p = 2) : d17596 p = 1 := by
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
  have h2 (q : Pattern) (selected : d350 q = 2) : d139 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d350, d139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro698 q selected
    | true =>
      simp only [d350, d139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d432 q = 2) : d227 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d432, d227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d432, d227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17663 q = 2) : d17593 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17663, d17593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17663, d17593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17664 q = 2) : d17594 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17664, d17594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17664, d17594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d245 q = 2) : d66 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d245, d66, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d245, d66, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro668 q selected
  have h7 (q : Pattern) (selected : d170 q = 2) : d25 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, d25, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro668 q selected
    | true =>
      simp only [d170, d25, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d246 q = 2) : d67 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246, d67, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d246, d67, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d17610 q = 2) : d17561 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17610, d17561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d17610, d17561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d17611 q = 2) : d17562 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17611, d17562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d17611, d17562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d17665 q = 2) : d17595 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17665, d17595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17665, d17595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d17612 q = 2) : d17563 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17612, d17563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d17612, d17563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d17666 q = 2) : d17596 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17666, d17596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d17666, d17596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro16420 (p : Pattern) (selected : d17672 p = 2) : d17602 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17667 q = 2) : d17597 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17667, d17597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16419 q selected
    | true =>
      simp only [d17667, d17597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16411 q selected
  have h2 (q : Pattern) (selected : d17668 q = 2) : d17598 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17668, d17598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17668, d17598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17669 q = 2) : d17599 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17669, d17599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17669, d17599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17614 q = 2) : d17565 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17614, d17565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16411 q selected
    | true =>
      simp only [d17614, d17565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17615 q = 2) : d17566 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17615, d17566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17615, d17566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17616 q = 2) : d17567 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17616, d17567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17616, d17567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d17670 q = 2) : d17600 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17670, d17600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17670, d17600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d17617 q = 2) : d17568 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17617, d17568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17617, d17568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d17671 q = 2) : d17601 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17671, d17601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d17671, d17601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d17672 q = 2) : d17602 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17672, d17602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d17672, d17602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16421 (p : Pattern) (selected : d17678 p = 2) : d17608 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17673 q = 2) : d17603 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17673, d17603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16420 q selected
    | true =>
      simp only [d17673, d17603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d17674 q = 2) : d17604 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17674, d17604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17674, d17604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17620 q = 2) : d17571 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17620, d17571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16412 q selected
    | true =>
      simp only [d17620, d17571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d17621 q = 2) : d17572 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17621, d17572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17621, d17572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d17675 q = 2) : d17605 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17675, d17605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d17675, d17605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17676 q = 2) : d17606 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17676, d17606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17676, d17606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d17677 q = 2) : d17607 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17677, d17607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17677, d17607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d17678 q = 2) : d17608 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17678, d17608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d17678, d17608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16422 (p : Pattern) (selected : d17684 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17603 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16409 q selected
    | true =>
      simp only [d17603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d17604 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17681 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d17681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d17682 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17683 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17684 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16423 (p : Pattern) (selected : d17690 p = 2) : d61093 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17662 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16418 q selected
    | true =>
      simp only [d17662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16410 q selected
  have h2 (q : Pattern) (selected : d17679 q = 2) : d17609 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17679, d17609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16421 q selected
    | true =>
      simp only [d17679, d17609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16413 q selected
  have h3 (q : Pattern) (selected : d17680 q = 2) : d61089 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17680, d61089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d17680, d61089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17685 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16422 q selected
    | true =>
      simp only [d17685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17686 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17687 q = 2) : d61090 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17687, d61090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17687, d61090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d17688 q = 2) : d61091 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17688, d61091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17688, d61091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d17689 q = 2) : d61092 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17689, d61092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17689, d61092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d17690 q = 2) : d61093 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17690, d61093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17690, d61093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16424 (p : Pattern) (selected : d17696 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17577 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16405 q selected
    | true =>
      simp only [d17577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d17692 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17693 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d17693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d17694 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d17695 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17696 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16425 (p : Pattern) (selected : d17702 p = 2) : d61099 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17691 q = 2) : d61094 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17691, d61094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17691, d61094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16423 q selected
  have h2 (q : Pattern) (selected : d17697 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16424 q selected
  have h3 (q : Pattern) (selected : d17698 q = 2) : d61095 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d17698, d61095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d17698, d61095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17699 q = 2) : d61096 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d17699, d61096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17699, d61096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17700 q = 2) : d61097 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d17700, d61097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17700, d61097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17701 q = 2) : d61098 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d17701, d61098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17701, d61098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d17702 q = 2) : d61099 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d17702, d61099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17702, d61099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16426 (p : Pattern) (selected : d17708 p = 2) : d61105 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17589 q = 2) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d17589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16407 q selected
  have h2 (q : Pattern) (selected : d17590 q = 2) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d17590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17591 q = 2) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d17591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17592 q = 2) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d17592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d17638 q = 2) : d61084 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d17638, d61084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17638, d61084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16415 q selected
  have h6 (q : Pattern) (selected : d17639 q = 2) : d61085 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d17639, d61085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17639, d61085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d17640 q = 2) : d61086 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d17640, d61086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17640, d61086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d17641 q = 2) : d61087 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d17641, d61087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17641, d61087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d17642 q = 2) : d61088 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d17642, d61088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17642, d61088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d17703 q = 2) : d61100 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d17703, d61100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17703, d61100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16425 q selected
  have h11 (q : Pattern) (selected : d17704 q = 2) : d61101 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d17704, d61101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17704, d61101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d17705 q = 2) : d61102 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d17705, d61102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17705, d61102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d17706 q = 2) : d61103 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d17706, d61103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17706, d61103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d17707 q = 2) : d61104 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d17707, d61104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17707, d61104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d17708 q = 2) : d61105 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d17708, d61105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d17708, d61105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro16427 (p : Pattern) (selected : d17717 p = 2) : d0 p = 1 := by
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
  have h2 (q : Pattern) (selected : d543 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro735 q selected
    | true =>
      simp only [d543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d660 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17709 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17710 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d16156 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10504 q selected
  have h7 (q : Pattern) (selected : d9458 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10504 q selected
    | true =>
      simp only [d9458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d16157 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d16157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d17711 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d17711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d17712 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d17712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d17713 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d12858 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10505 q selected
  have h13 (q : Pattern) (selected : d9468 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10505 q selected
    | true =>
      simp only [d9468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d12859 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d12859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d17714 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d17714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d17715 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d17715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d12599 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10492 q selected
  have h18 (q : Pattern) (selected : d9382 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10492 q selected
    | true =>
      simp only [d9382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d12600 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d12600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d17646 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d17646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d17647 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d17647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d17716 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d17716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d17717 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d17717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro16428 (p : Pattern) (selected : d17721 p = 2) : d0 p = 1 := by
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
  have h2 (q : Pattern) (selected : d9382 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10492 q selected
    | true =>
      simp only [d9382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d12600 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17646 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17647 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d66 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d66, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro645 q selected
  have h7 (q : Pattern) (selected : d25 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro645 q selected
    | true =>
      simp only [d25, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d67 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d67, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d17561 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d17561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d17562 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d17562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d17648 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d17563 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d17563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d17721 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d17721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro16429 (p : Pattern) (selected : d17727 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17718 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16427 q selected
    | true =>
      simp only [d17718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16416 q selected
  have h2 (q : Pattern) (selected : d17719 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17720 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17722 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16416 q selected
    | true =>
      simp only [d17722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16428 q selected
  have h5 (q : Pattern) (selected : d17723 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17724 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d17725 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d17650 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16416 q selected
    | true =>
      simp only [d17650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16408 q selected
  have h9 (q : Pattern) (selected : d17651 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d17652 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d17597 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16408 q selected
    | true =>
      simp only [d17597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16403 q selected
  have h12 (q : Pattern) (selected : d17598 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d17599 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d17653 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d17653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d17726 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d17726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d17727 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d17727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro16430 (p : Pattern) (selected : d17732 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17650 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16416 q selected
    | true =>
      simp only [d17650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16408 q selected
  have h2 (q : Pattern) (selected : d17651 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17652 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17597 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16408 q selected
    | true =>
      simp only [d17597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16403 q selected
  have h5 (q : Pattern) (selected : d17598 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17599 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d17653 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d17730 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d17731 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d17731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d17732 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d17732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16431 (p : Pattern) (selected : d17738 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17728 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16429 q selected
    | true =>
      simp only [d17728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d17729 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17733 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16430 q selected
    | true =>
      simp only [d17733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d17734 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d17735 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d17735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17736 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d17737 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d17738 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d17738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16432 (p : Pattern) (selected : d17740 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17597 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16408 q selected
    | true =>
      simp only [d17597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16403 q selected
  have h2 (q : Pattern) (selected : d17598 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17599 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17730 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17739 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17740 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16433 (p : Pattern) (selected : d17746 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17733 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16430 q selected
    | true =>
      simp only [d17733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d17734 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17741 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16432 q selected
    | true =>
      simp only [d17741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d17742 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d17743 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d17743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17744 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d17745 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d17746 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d17746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16434 (p : Pattern) (selected : d17754 p = 2) : d17649 p = 1 := by
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
  have h2 (q : Pattern) (selected : d574 q = 2) : d319 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d574, d319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro740 q selected
    | true =>
      simp only [d574, d319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d692 q = 2) : d413 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d692, d413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d692, d413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17748 q = 2) : d17643 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17748, d17643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17748, d17643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17749 q = 2) : d17644 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17749, d17644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17749, d17644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d431 q = 2) : d226 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d431, d226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d431, d226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro698 q selected
  have h7 (q : Pattern) (selected : d350 q = 2) : d139 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d350, d139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro698 q selected
    | true =>
      simp only [d350, d139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d432 q = 2) : d227 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d432, d227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d432, d227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d17663 q = 2) : d17593 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17663, d17593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d17663, d17593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d17664 q = 2) : d17594 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17664, d17594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d17664, d17594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d17750 q = 2) : d17645 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17750, d17645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17750, d17645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d14404 q = 2) : d12599 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14404, d12599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14404, d12599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10513 q selected
  have h13 (q : Pattern) (selected : d9512 q = 2) : d9382 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9512, d9382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10513 q selected
    | true =>
      simp only [d9512, d9382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d14405 q = 2) : d12600 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14405, d12600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d14405, d12600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d17751 q = 2) : d17646 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17751, d17646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d17751, d17646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d17752 q = 2) : d17647 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17752, d17647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d17752, d17647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d245 q = 2) : d66 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d245, d66, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d245, d66, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro668 q selected
  have h18 (q : Pattern) (selected : d170 q = 2) : d25 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, d25, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro668 q selected
    | true =>
      simp only [d170, d25, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d246 q = 2) : d67 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246, d67, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d246, d67, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d17610 q = 2) : d17561 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17610, d17561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d17610, d17561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d17611 q = 2) : d17562 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17611, d17562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d17611, d17562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d17753 q = 2) : d17648 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17753, d17648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d17753, d17648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d17754 q = 2) : d17649 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17754, d17649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d17754, d17649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro16435 (p : Pattern) (selected : d17761 p = 2) : d17732 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17755 q = 2) : d17650 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17755, d17650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16434 q selected
    | true =>
      simp only [d17755, d17650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16419 q selected
  have h2 (q : Pattern) (selected : d17756 q = 2) : d17651 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17756, d17651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17756, d17651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17757 q = 2) : d17652 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17757, d17652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17757, d17652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17667 q = 2) : d17597 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17667, d17597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16419 q selected
    | true =>
      simp only [d17667, d17597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16411 q selected
  have h5 (q : Pattern) (selected : d17668 q = 2) : d17598 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17668, d17598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17668, d17598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17669 q = 2) : d17599 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17669, d17599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17669, d17599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d17758 q = 2) : d17653 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17758, d17653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17758, d17653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d17759 q = 2) : d17730 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17759, d17730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17759, d17730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d17760 q = 2) : d17731 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17760, d17731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d17760, d17731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d17761 q = 2) : d17732 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17761, d17732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d17761, d17732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16436 (p : Pattern) (selected : d17765 p = 2) : d17740 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17667 q = 2) : d17597 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17667, d17597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16419 q selected
    | true =>
      simp only [d17667, d17597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16411 q selected
  have h2 (q : Pattern) (selected : d17668 q = 2) : d17598 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17668, d17598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17668, d17598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17669 q = 2) : d17599 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17669, d17599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17669, d17599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17759 q = 2) : d17730 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17759, d17730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17759, d17730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17764 q = 2) : d17739 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17764, d17739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17764, d17739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17765 q = 2) : d17740 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17765, d17740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17765, d17740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16437 (p : Pattern) (selected : d17771 p = 2) : d17746 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17762 q = 2) : d17733 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17762, d17733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16435 q selected
    | true =>
      simp only [d17762, d17733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d17763 q = 2) : d17734 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17763, d17734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17763, d17734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17766 q = 2) : d17741 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17766, d17741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16436 q selected
    | true =>
      simp only [d17766, d17741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d17767 q = 2) : d17742 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17767, d17742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17767, d17742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d17768 q = 2) : d17743 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17768, d17743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d17768, d17743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17769 q = 2) : d17744 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17769, d17744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17769, d17744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d17770 q = 2) : d17745 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17770, d17745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17770, d17745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d17771 q = 2) : d17746 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17771, d17746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d17771, d17746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16438 (p : Pattern) (selected : d17775 p = 2) : d17792 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17766 q = 2) : d17741 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17766, d17741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16436 q selected
    | true =>
      simp only [d17766, d17741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d17767 q = 2) : d17742 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17767, d17742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17767, d17742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17772 q = 2) : d17789 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17772, d17789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d17772, d17789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d17773 q = 2) : d17790 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17773, d17790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17773, d17790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17774 q = 2) : d17791 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17774, d17791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17774, d17791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17775 q = 2) : d17792 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17775, d17792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17775, d17792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16439 (p : Pattern) (selected : d17781 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17733 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16430 q selected
    | true =>
      simp only [d17733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d17734 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17778 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d17778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d17779 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17780 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17781 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16440 (p : Pattern) (selected : d17787 p = 2) : d173535 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17747 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16431 q selected
    | true =>
      simp only [d17747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16433 q selected
  have h2 (q : Pattern) (selected : d17776 q = 2) : d173530 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17776, d173530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16437 q selected
    | true =>
      simp only [d17776, d173530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16438 q selected
  have h3 (q : Pattern) (selected : d17777 q = 2) : d173531 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17777, d173531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d17777, d173531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17782 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16439 q selected
    | true =>
      simp only [d17782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17783 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17784 q = 2) : d173532 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17784, d173532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17784, d173532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d17785 q = 2) : d173533 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17785, d173533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17785, d173533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d17786 q = 2) : d173534 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17786, d173534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17786, d173534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d17787 q = 2) : d173535 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17787, d173535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17787, d173535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16441 (p : Pattern) (selected : d17792 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17741 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16432 q selected
    | true =>
      simp only [d17741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d17742 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17789 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d17789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d17790 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17791 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17792 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16442 (p : Pattern) (selected : d17798 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17793 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16441 q selected
    | true =>
      simp only [d17793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d17794 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17795 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d17795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d17796 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d17797 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17798 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16443 (p : Pattern) (selected : d17804 p = 2) : d173541 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17788 q = 2) : d173536 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17788, d173536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17788, d173536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16440 q selected
  have h2 (q : Pattern) (selected : d17799 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16442 q selected
  have h3 (q : Pattern) (selected : d17800 q = 2) : d173537 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d17800, d173537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d17800, d173537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17801 q = 2) : d173538 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d17801, d173538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17801, d173538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17802 q = 2) : d173539 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d17802, d173539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17802, d173539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17803 q = 2) : d173540 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d17803, d173540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17803, d173540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d17804 q = 2) : d173541 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d17804, d173541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17804, d173541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16444 (p : Pattern) (selected : d17810 p = 2) : d173547 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17805 q = 2) : d173542 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d17805, d173542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17805, d173542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16443 q selected
  have h2 (q : Pattern) (selected : d17806 q = 2) : d173543 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d17806, d173543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17806, d173543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17807 q = 2) : d173544 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d17807, d173544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17807, d173544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17808 q = 2) : d173545 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d17808, d173545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17808, d173545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d17809 q = 2) : d173546 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d17809, d173546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17809, d173546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17810 q = 2) : d173547 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d17810, d173547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17810, d173547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16445 (p : Pattern) (selected : d17820 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d965 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro793 q selected
  have h2 (q : Pattern) (selected : d834 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro793 q selected
    | true =>
      simp only [d834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d966 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17812 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17813 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d16356 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10526 q selected
  have h7 (q : Pattern) (selected : d9587 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10526 q selected
    | true =>
      simp only [d9587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d16357 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d16357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d17814 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d17814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d17815 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d17815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d17816 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d14644 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10527 q selected
  have h13 (q : Pattern) (selected : d9597 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10527 q selected
    | true =>
      simp only [d9597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d14645 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d14645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d17817 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d17817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d17818 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d17818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d12858 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10505 q selected
  have h18 (q : Pattern) (selected : d9468 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10505 q selected
    | true =>
      simp only [d9468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d12859 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d12859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d17714 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d17714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d17715 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d17715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d17819 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d17819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d17820 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d17820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro16446 (p : Pattern) (selected : d17824 p = 2) : d0 p = 1 := by
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
  have h2 (q : Pattern) (selected : d543 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro735 q selected
    | true =>
      simp only [d543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d660 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17709 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17710 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d16156 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10504 q selected
  have h7 (q : Pattern) (selected : d9458 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10504 q selected
    | true =>
      simp only [d9458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d16157 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d16157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d17711 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d17711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d17712 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d17712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d17713 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d12858 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10505 q selected
  have h13 (q : Pattern) (selected : d9468 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10505 q selected
    | true =>
      simp only [d9468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d12859 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d12859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d17714 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d17714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d17715 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d17715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d971 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro775 q selected
  have h18 (q : Pattern) (selected : d751 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro775 q selected
    | true =>
      simp only [d751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d972 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d17821 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d17821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d17822 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d17822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d17823 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d17823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d17824 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d17824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro16447 (p : Pattern) (selected : d17829 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d12858 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10505 q selected
  have h2 (q : Pattern) (selected : d9468 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10505 q selected
    | true =>
      simp only [d9468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d12859 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17714 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17715 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d971 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro775 q selected
  have h7 (q : Pattern) (selected : d751 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro775 q selected
    | true =>
      simp only [d751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d972 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d17821 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d17821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d17822 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d17822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d17823 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d17828 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d17828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d17829 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d17829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro16448 (p : Pattern) (selected : d17835 p = 2) : d0 p = 1 := by
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
  have h2 (q : Pattern) (selected : d319 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro693 q selected
    | true =>
      simp only [d319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d413 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17643 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17644 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d971 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro775 q selected
  have h7 (q : Pattern) (selected : d751 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro775 q selected
    | true =>
      simp only [d751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d972 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d17821 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d17821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d17822 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d17822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d17834 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d17828 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d17828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d17835 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d17835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro16449 (p : Pattern) (selected : d17839 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d971 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro775 q selected
  have h2 (q : Pattern) (selected : d751 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro775 q selected
    | true =>
      simp only [d751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d972 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17821 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17822 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17828 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d17839 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro16450 (p : Pattern) (selected : d17845 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17825 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16445 q selected
    | true =>
      simp only [d17825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16446 q selected
  have h2 (q : Pattern) (selected : d17826 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17827 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17830 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16446 q selected
    | true =>
      simp only [d17830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16447 q selected
  have h5 (q : Pattern) (selected : d17831 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17832 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d17833 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d17836 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16446 q selected
    | true =>
      simp only [d17836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16448 q selected
  have h9 (q : Pattern) (selected : d17837 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d17838 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d17840 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16448 q selected
    | true =>
      simp only [d17840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16449 q selected
  have h12 (q : Pattern) (selected : d17841 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d17842 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d17843 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d17843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d17844 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d17844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d17845 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d17845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro16451 (p : Pattern) (selected : d17850 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17836 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16446 q selected
    | true =>
      simp only [d17836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16448 q selected
  have h2 (q : Pattern) (selected : d17837 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17838 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17840 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16448 q selected
    | true =>
      simp only [d17840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16449 q selected
  have h5 (q : Pattern) (selected : d17841 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17842 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d17843 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d17848 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d17849 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d17849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d17850 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d17850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16452 (p : Pattern) (selected : d17856 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17846 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16450 q selected
    | true =>
      simp only [d17846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d17847 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17851 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16451 q selected
    | true =>
      simp only [d17851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d17852 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d17853 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d17853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17854 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d17855 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d17856 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d17856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16453 (p : Pattern) (selected : d17858 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17840 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16448 q selected
    | true =>
      simp only [d17840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16449 q selected
  have h2 (q : Pattern) (selected : d17841 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17842 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17848 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17857 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17858 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16454 (p : Pattern) (selected : d17864 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17851 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16451 q selected
    | true =>
      simp only [d17851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d17852 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17859 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16453 q selected
    | true =>
      simp only [d17859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d17860 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d17861 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d17861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17862 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d17863 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d17864 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d17864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16455 (p : Pattern) (selected : d17876 p = 2) : d17824 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1013 q = 2) : d659 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1013, d659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1013, d659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro799 q selected
  have h2 (q : Pattern) (selected : d868 q = 2) : d543 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d868, d543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro799 q selected
    | true =>
      simp only [d868, d543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1014 q = 2) : d660 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1014, d660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1014, d660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17866 q = 2) : d17709 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17866, d17709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17866, d17709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17867 q = 2) : d17710 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17867, d17710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17867, d17710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d16393 q = 2) : d16156 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16393, d16156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16393, d16156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10539 q selected
  have h7 (q : Pattern) (selected : d9661 q = 2) : d9458 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9661, d9458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10539 q selected
    | true =>
      simp only [d9661, d9458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d16394 q = 2) : d16157 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16394, d16157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d16394, d16157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d17868 q = 2) : d17711 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17868, d17711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d17868, d17711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d17869 q = 2) : d17712 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17869, d17712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d17869, d17712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d17870 q = 2) : d17713 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17870, d17713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17870, d17713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d14689 q = 2) : d12858 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14689, d12858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14689, d12858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10540 q selected
  have h13 (q : Pattern) (selected : d9671 q = 2) : d9468 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9671, d9468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10540 q selected
    | true =>
      simp only [d9671, d9468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d14690 q = 2) : d12859 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14690, d12859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d14690, d12859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d17871 q = 2) : d17714 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17871, d17714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d17871, d17714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d17872 q = 2) : d17715 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17872, d17715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d17872, d17715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d1018 q = 2) : d971 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1018, d971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1018, d971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro800 q selected
  have h18 (q : Pattern) (selected : d874 q = 2) : d751 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, d751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro800 q selected
    | true =>
      simp only [d874, d751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d1019 q = 2) : d972 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1019, d972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d1019, d972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d17873 q = 2) : d17821 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17873, d17821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d17873, d17821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d17874 q = 2) : d17822 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17874, d17822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d17874, d17822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d17875 q = 2) : d17823 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17875, d17823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d17875, d17823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d17876 q = 2) : d17824 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17876, d17824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d17876, d17824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro16456 (p : Pattern) (selected : d17879 p = 2) : d17835 p = 1 := by
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
  have h2 (q : Pattern) (selected : d574 q = 2) : d319 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d574, d319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro740 q selected
    | true =>
      simp only [d574, d319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d692 q = 2) : d413 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d692, d413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d692, d413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17748 q = 2) : d17643 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17748, d17643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17748, d17643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17749 q = 2) : d17644 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17749, d17644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17749, d17644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d1018 q = 2) : d971 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1018, d971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1018, d971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro800 q selected
  have h7 (q : Pattern) (selected : d874 q = 2) : d751 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, d751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro800 q selected
    | true =>
      simp only [d874, d751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d1019 q = 2) : d972 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1019, d972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1019, d972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d17873 q = 2) : d17821 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17873, d17821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d17873, d17821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d17874 q = 2) : d17822 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17874, d17822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d17874, d17822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d17877 q = 2) : d17834 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17877, d17834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17877, d17834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d17878 q = 2) : d17828 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17878, d17828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d17878, d17828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d17879 q = 2) : d17835 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17879, d17835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d17879, d17835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro16457 (p : Pattern) (selected : d17883 p = 2) : d17839 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1018 q = 2) : d971 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1018, d971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1018, d971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro800 q selected
  have h2 (q : Pattern) (selected : d874 q = 2) : d751 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, d751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro800 q selected
    | true =>
      simp only [d874, d751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1019 q = 2) : d972 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1019, d972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1019, d972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17873 q = 2) : d17821 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17873, d17821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17873, d17821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17874 q = 2) : d17822 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17874, d17822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17874, d17822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17878 q = 2) : d17828 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17878, d17828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17878, d17828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d17883 q = 2) : d17839 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17883, d17839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17883, d17839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro16458 (p : Pattern) (selected : d17890 p = 2) : d17850 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17880 q = 2) : d17836 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17880, d17836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16455 q selected
    | true =>
      simp only [d17880, d17836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16456 q selected
  have h2 (q : Pattern) (selected : d17881 q = 2) : d17837 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17881, d17837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17881, d17837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17882 q = 2) : d17838 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17882, d17838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17882, d17838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17884 q = 2) : d17840 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17884, d17840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16456 q selected
    | true =>
      simp only [d17884, d17840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16457 q selected
  have h5 (q : Pattern) (selected : d17885 q = 2) : d17841 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17885, d17841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17885, d17841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17886 q = 2) : d17842 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17886, d17842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17886, d17842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d17887 q = 2) : d17843 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17887, d17843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17887, d17843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d17888 q = 2) : d17848 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17888, d17848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17888, d17848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d17889 q = 2) : d17849 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17889, d17849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d17889, d17849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d17890 q = 2) : d17850 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17890, d17850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d17890, d17850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16459 (p : Pattern) (selected : d17894 p = 2) : d17858 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17884 q = 2) : d17840 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17884, d17840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16456 q selected
    | true =>
      simp only [d17884, d17840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16457 q selected
  have h2 (q : Pattern) (selected : d17885 q = 2) : d17841 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17885, d17841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17885, d17841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17886 q = 2) : d17842 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17886, d17842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17886, d17842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17888 q = 2) : d17848 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17888, d17848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17888, d17848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17893 q = 2) : d17857 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17893, d17857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17893, d17857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17894 q = 2) : d17858 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17894, d17858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17894, d17858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16460 (p : Pattern) (selected : d17900 p = 2) : d17864 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17891 q = 2) : d17851 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17891, d17851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16458 q selected
    | true =>
      simp only [d17891, d17851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d17892 q = 2) : d17852 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17892, d17852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17892, d17852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17895 q = 2) : d17859 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17895, d17859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16459 q selected
    | true =>
      simp only [d17895, d17859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d17896 q = 2) : d17860 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17896, d17860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17896, d17860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d17897 q = 2) : d17861 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17897, d17861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d17897, d17861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17898 q = 2) : d17862 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17898, d17862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17898, d17862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d17899 q = 2) : d17863 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17899, d17863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17899, d17863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d17900 q = 2) : d17864 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17900, d17864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d17900, d17864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16461 (p : Pattern) (selected : d17904 p = 2) : d17921 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17895 q = 2) : d17859 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17895, d17859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16459 q selected
    | true =>
      simp only [d17895, d17859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d17896 q = 2) : d17860 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17896, d17860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17896, d17860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17901 q = 2) : d17918 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17901, d17918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d17901, d17918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d17902 q = 2) : d17919 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17902, d17919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17902, d17919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17903 q = 2) : d17920 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17903, d17920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17903, d17920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17904 q = 2) : d17921 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17904, d17921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17904, d17921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16462 (p : Pattern) (selected : d17910 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17851 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16451 q selected
    | true =>
      simp only [d17851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d17852 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17907 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d17907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d17908 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17909 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17910 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16463 (p : Pattern) (selected : d17916 p = 2) : d173554 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17865 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16452 q selected
    | true =>
      simp only [d17865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16454 q selected
  have h2 (q : Pattern) (selected : d17905 q = 2) : d173549 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17905, d173549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16460 q selected
    | true =>
      simp only [d17905, d173549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16461 q selected
  have h3 (q : Pattern) (selected : d17906 q = 2) : d173550 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17906, d173550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d17906, d173550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17911 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16462 q selected
    | true =>
      simp only [d17911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17912 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17913 q = 2) : d173551 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17913, d173551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17913, d173551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d17914 q = 2) : d173552 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17914, d173552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17914, d173552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d17915 q = 2) : d173553 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17915, d173553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17915, d173553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d17916 q = 2) : d173554 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17916, d173554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17916, d173554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16464 (p : Pattern) (selected : d17921 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17859 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16453 q selected
    | true =>
      simp only [d17859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d17860 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17918 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d17918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d17918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d17919 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d17919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17920 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d17920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17921 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d17921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16465 (p : Pattern) (selected : d17927 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17922 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d17922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16464 q selected
    | true =>
      simp only [d17922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d17923 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d17923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17924 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d17924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d17924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d17925 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d17925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d17926 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d17926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17927 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d17927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16466 (p : Pattern) (selected : d17933 p = 2) : d173560 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17917 q = 2) : d173555 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17917, d173555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17917, d173555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16463 q selected
  have h2 (q : Pattern) (selected : d17928 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d17928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16465 q selected
  have h3 (q : Pattern) (selected : d17929 q = 2) : d173556 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d17929, d173556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d17929, d173556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17930 q = 2) : d173557 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d17930, d173557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17930, d173557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17931 q = 2) : d173558 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d17931, d173558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17931, d173558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17932 q = 2) : d173559 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d17932, d173559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17932, d173559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d17933 q = 2) : d173560 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d17933, d173560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17933, d173560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16467 (p : Pattern) (selected : d17939 p = 2) : d173566 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17934 q = 2) : d173561 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d17934, d173561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17934, d173561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16466 q selected
  have h2 (q : Pattern) (selected : d17935 q = 2) : d173562 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d17935, d173562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17935, d173562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17936 q = 2) : d173563 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d17936, d173563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17936, d173563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17937 q = 2) : d173564 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d17937, d173564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17937, d173564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d17938 q = 2) : d173565 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d17938, d173565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17938, d173565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17939 q = 2) : d173566 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d17939, d173566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17939, d173566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16468 (p : Pattern) (selected : d17952 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1376 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro865 q selected
  have h2 (q : Pattern) (selected : d1210 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro865 q selected
    | true =>
      simp only [d1210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1377 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17942 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17943 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d16649 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10554 q selected
  have h7 (q : Pattern) (selected : d9753 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10554 q selected
    | true =>
      simp only [d9753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d16650 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d16650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d17944 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d17944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d17945 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d17945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d17946 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d14987 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10555 q selected
  have h13 (q : Pattern) (selected : d9763 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10555 q selected
    | true =>
      simp only [d9763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d14988 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d14988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d17947 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d17947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d17948 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d17948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d14994 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10557 q selected
  have h18 (q : Pattern) (selected : d9778 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10557 q selected
    | true =>
      simp only [d9778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d14995 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d14995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d17949 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d17949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d17950 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d17950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d17951 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d17951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d17952 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d17952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro16469 (p : Pattern) (selected : d17961 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1380 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro844 q selected
  have h2 (q : Pattern) (selected : d1100 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro844 q selected
    | true =>
      simp only [d1100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1381 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17953 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17954 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d16656 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10559 q selected
  have h7 (q : Pattern) (selected : d9789 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10559 q selected
    | true =>
      simp only [d9789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d16657 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d16657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d17955 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d17955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d17956 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d17956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d17957 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d14994 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d14994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10557 q selected
  have h13 (q : Pattern) (selected : d9778 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10557 q selected
    | true =>
      simp only [d9778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d14995 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d14995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d17949 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d17949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d17950 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d17950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d15004 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10560 q selected
  have h18 (q : Pattern) (selected : d9800 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10560 q selected
    | true =>
      simp only [d9800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d15005 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d15005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d17958 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d17958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d17959 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d17959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d17960 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d17960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d17961 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d17961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro16470 (p : Pattern) (selected : d17969 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13160 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10562 q selected
  have h2 (q : Pattern) (selected : d9814 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10562 q selected
    | true =>
      simp only [d9814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13161 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17965 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17966 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15004 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10560 q selected
  have h7 (q : Pattern) (selected : d9800 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10560 q selected
    | true =>
      simp only [d9800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15005 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d17958 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d17958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d17959 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d17959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d17967 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d17968 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d17968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d17969 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d17969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro16471 (p : Pattern) (selected : d17979 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1385 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro845 q selected
  have h2 (q : Pattern) (selected : d1110 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro845 q selected
    | true =>
      simp only [d1110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1386 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17974 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17975 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d1391 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro846 q selected
  have h7 (q : Pattern) (selected : d1121 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro846 q selected
    | true =>
      simp only [d1121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d1392 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d17976 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d17976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d17977 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d17977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d17978 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d15004 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10560 q selected
  have h13 (q : Pattern) (selected : d9800 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10560 q selected
    | true =>
      simp only [d9800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15005 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d17958 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d17958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d17959 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d17959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d17968 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d17968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d17979 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d17979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro16472 (p : Pattern) (selected : d17989 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6350 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3843 q selected
  have h2 (q : Pattern) (selected : d5018 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3843 q selected
    | true =>
      simp only [d5018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d6351 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d6351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17983 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17984 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17985 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d17985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15019 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10565 q selected
  have h8 (q : Pattern) (selected : d9844 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10565 q selected
    | true =>
      simp only [d9844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d15020 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d17986 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d17986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d17987 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d17987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d17988 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d17988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d17989 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d17989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro16473 (p : Pattern) (selected : d17995 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17962 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16468 q selected
    | true =>
      simp only [d17962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16469 q selected
  have h2 (q : Pattern) (selected : d17963 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17964 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17970 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16469 q selected
    | true =>
      simp only [d17970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16470 q selected
  have h5 (q : Pattern) (selected : d17971 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17972 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d17973 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d17980 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16469 q selected
    | true =>
      simp only [d17980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16471 q selected
  have h9 (q : Pattern) (selected : d17981 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d17982 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d17990 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16471 q selected
    | true =>
      simp only [d17990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16472 q selected
  have h12 (q : Pattern) (selected : d17991 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d17992 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d17993 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d17993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d17994 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d17994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d17995 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d17995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d17995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro16474 (p : Pattern) (selected : d18000 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17980 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16469 q selected
    | true =>
      simp only [d17980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16471 q selected
  have h2 (q : Pattern) (selected : d17981 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17982 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17990 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16471 q selected
    | true =>
      simp only [d17990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16472 q selected
  have h5 (q : Pattern) (selected : d17991 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17992 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d17993 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d17998 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d17999 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d17999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d18000 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d18000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro16475 (p : Pattern) (selected : d18006 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17996 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d17996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16473 q selected
    | true =>
      simp only [d17996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d17997 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d17997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18001 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16474 q selected
    | true =>
      simp only [d18001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18002 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d18003 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18004 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d18005 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d18006 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d18006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16476 (p : Pattern) (selected : d18008 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1391 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro846 q selected
  have h2 (q : Pattern) (selected : d1121 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro846 q selected
    | true =>
      simp only [d1121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1392 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17976 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17977 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18007 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15019 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10565 q selected
  have h8 (q : Pattern) (selected : d9844 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10565 q selected
    | true =>
      simp only [d9844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d15020 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d17986 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d17986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d17987 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d17987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d17988 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d17988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d17988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d18008 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro16477 (p : Pattern) (selected : d18014 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18009 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16471 q selected
    | true =>
      simp only [d18009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16476 q selected
  have h2 (q : Pattern) (selected : d18010 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18011 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18012 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18013 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18014 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16478 (p : Pattern) (selected : d18020 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18001 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16474 q selected
    | true =>
      simp only [d18001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18002 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18015 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16477 q selected
    | true =>
      simp only [d18015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18016 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d18017 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18018 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d18019 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d18020 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d18020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16479 (p : Pattern) (selected : d18032 p = 2) : d17961 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1438 q = 2) : d1380 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1438, d1380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1438, d1380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro873 q selected
  have h2 (q : Pattern) (selected : d1255 q = 2) : d1100 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1255, d1100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro873 q selected
    | true =>
      simp only [d1255, d1100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1439 q = 2) : d1381 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1439, d1381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1439, d1381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18022 q = 2) : d17953 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18022, d17953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18022, d17953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18023 q = 2) : d17954 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18023, d17954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18023, d17954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d16706 q = 2) : d16656 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16706, d16656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16706, d16656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10575 q selected
  have h7 (q : Pattern) (selected : d9896 q = 2) : d9789 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9896, d9789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10575 q selected
    | true =>
      simp only [d9896, d9789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d16707 q = 2) : d16657 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16707, d16657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d16707, d16657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d18024 q = 2) : d17955 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18024, d17955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d18024, d17955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d18025 q = 2) : d17956 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18025, d17956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d18025, d17956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d18026 q = 2) : d17957 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18026, d17957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18026, d17957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d15057 q = 2) : d14994 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15057, d14994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15057, d14994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10576 q selected
  have h13 (q : Pattern) (selected : d9908 q = 2) : d9778 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9908, d9778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10576 q selected
    | true =>
      simp only [d9908, d9778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15058 q = 2) : d14995 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15058, d14995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15058, d14995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d18027 q = 2) : d17949 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18027, d17949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d18027, d17949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d18028 q = 2) : d17950 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18028, d17950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d18028, d17950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d15064 q = 2) : d15004 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15064, d15004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15064, d15004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10577 q selected
  have h18 (q : Pattern) (selected : d9918 q = 2) : d9800 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9918, d9800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10577 q selected
    | true =>
      simp only [d9918, d9800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d15065 q = 2) : d15005 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15065, d15005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d15065, d15005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d18029 q = 2) : d17958 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18029, d17958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d18029, d17958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d18030 q = 2) : d17959 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18030, d17959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d18030, d17959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d18031 q = 2) : d17960 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18031, d17960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d18031, d17960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d18032 q = 2) : d17961 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18032, d17961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d18032, d17961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro16480 (p : Pattern) (selected : d18039 p = 2) : d17979 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1442 q = 2) : d1385 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1442, d1385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1442, d1385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro874 q selected
  have h2 (q : Pattern) (selected : d1265 q = 2) : d1110 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1265, d1110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro874 q selected
    | true =>
      simp only [d1265, d1110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1443 q = 2) : d1386 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1443, d1386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1443, d1386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18033 q = 2) : d17974 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18033, d17974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18033, d17974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18034 q = 2) : d17975 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18034, d17975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18034, d17975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d1447 q = 2) : d1391 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1447, d1391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1447, d1391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro875 q selected
  have h7 (q : Pattern) (selected : d1276 q = 2) : d1121 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1276, d1121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro875 q selected
    | true =>
      simp only [d1276, d1121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d1448 q = 2) : d1392 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1448, d1392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1448, d1392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d18035 q = 2) : d17976 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18035, d17976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d18035, d17976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d18036 q = 2) : d17977 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18036, d17977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d18036, d17977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d18037 q = 2) : d17978 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18037, d17978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18037, d17978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d15064 q = 2) : d15004 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15064, d15004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15064, d15004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10577 q selected
  have h13 (q : Pattern) (selected : d9918 q = 2) : d9800 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9918, d9800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10577 q selected
    | true =>
      simp only [d9918, d9800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15065 q = 2) : d15005 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15065, d15005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15065, d15005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d18029 q = 2) : d17958 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18029, d17958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d18029, d17958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d18030 q = 2) : d17959 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18030, d17959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d18030, d17959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d18038 q = 2) : d17968 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18038, d17968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d18038, d17968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d18039 q = 2) : d17979 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18039, d17979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d18039, d17979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro16481 (p : Pattern) (selected : d18049 p = 2) : d17989 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13209 q = 2) : d6350 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13209, d6350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13209, d6350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10580 q selected
  have h2 (q : Pattern) (selected : d9943 q = 2) : d5018 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9943, d5018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10580 q selected
    | true =>
      simp only [d9943, d5018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13210 q = 2) : d6351 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13210, d6351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13210, d6351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18043 q = 2) : d17983 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18043, d17983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18043, d17983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18044 q = 2) : d17984 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18044, d17984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18044, d17984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18045 q = 2) : d17985 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18045, d17985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18045, d17985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15073 q = 2) : d15019 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15073, d15019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15073, d15019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10581 q selected
  have h8 (q : Pattern) (selected : d9952 q = 2) : d9844 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9952, d9844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10581 q selected
    | true =>
      simp only [d9952, d9844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d15074 q = 2) : d15020 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15074, d15020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15074, d15020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d18046 q = 2) : d17986 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18046, d17986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d18046, d17986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d18047 q = 2) : d17987 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18047, d17987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d18047, d17987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d18048 q = 2) : d17988 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18048, d17988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d18048, d17988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d18049 q = 2) : d17989 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18049, d17989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18049, d17989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro16482 (p : Pattern) (selected : d18055 p = 2) : d18008 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1447 q = 2) : d1391 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1447, d1391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1447, d1391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro875 q selected
  have h2 (q : Pattern) (selected : d1276 q = 2) : d1121 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1276, d1121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro875 q selected
    | true =>
      simp only [d1276, d1121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1448 q = 2) : d1392 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1448, d1392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1448, d1392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18035 q = 2) : d17976 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18035, d17976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18035, d17976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18036 q = 2) : d17977 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18036, d17977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18036, d17977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18054 q = 2) : d18007 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18054, d18007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18054, d18007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15073 q = 2) : d15019 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15073, d15019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15073, d15019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10581 q selected
  have h8 (q : Pattern) (selected : d9952 q = 2) : d9844 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9952, d9844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10581 q selected
    | true =>
      simp only [d9952, d9844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d15074 q = 2) : d15020 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15074, d15020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15074, d15020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d18046 q = 2) : d17986 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18046, d17986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d18046, d17986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d18047 q = 2) : d17987 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18047, d17987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d18047, d17987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d18048 q = 2) : d17988 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18048, d17988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d18048, d17988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d18055 q = 2) : d18008 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18055, d18008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18055, d18008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro16483 (p : Pattern) (selected : d18061 p = 2) : d173570 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18040 q = 2) : d17980 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18040, d17980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16479 q selected
    | true =>
      simp only [d18040, d17980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16480 q selected
  have h2 (q : Pattern) (selected : d18041 q = 2) : d17981 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18041, d17981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18041, d17981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18042 q = 2) : d17982 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18042, d17982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18042, d17982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18050 q = 2) : d17990 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18050, d17990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16480 q selected
    | true =>
      simp only [d18050, d17990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16481 q selected
  have h5 (q : Pattern) (selected : d18051 q = 2) : d17991 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18051, d17991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18051, d17991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18052 q = 2) : d17992 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18052, d17992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18052, d17992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d18053 q = 2) : d17993 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18053, d17993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18053, d17993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d18056 q = 2) : d18009 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18056, d18009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16480 q selected
    | true =>
      simp only [d18056, d18009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16482 q selected
  have h9 (q : Pattern) (selected : d18057 q = 2) : d18010 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18057, d18010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18057, d18010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d18058 q = 2) : d18011 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18058, d18011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18058, d18011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d18059 q = 2) : d18012 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18059, d18012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d18059, d18012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d18060 q = 2) : d173569 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18060, d173569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d18060, d173569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d18061 q = 2) : d173570 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18061, d173570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d18061, d173570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro16484 (p : Pattern) (selected : d18065 p = 2) : d18014 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18056 q = 2) : d18009 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18056, d18009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16480 q selected
    | true =>
      simp only [d18056, d18009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16482 q selected
  have h2 (q : Pattern) (selected : d18057 q = 2) : d18010 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18057, d18010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18057, d18010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18058 q = 2) : d18011 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18058, d18011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18058, d18011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18059 q = 2) : d18012 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18059, d18012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18059, d18012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18064 q = 2) : d18013 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18064, d18013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18064, d18013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18065 q = 2) : d18014 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18065, d18014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18065, d18014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16485 (p : Pattern) (selected : d18071 p = 2) : d173576 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18062 q = 2) : d173571 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18062, d173571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16483 q selected
    | true =>
      simp only [d18062, d173571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18063 q = 2) : d173572 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18063, d173572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18063, d173572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18066 q = 2) : d18015 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18066, d18015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16484 q selected
    | true =>
      simp only [d18066, d18015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18067 q = 2) : d18016 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18067, d18016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18067, d18016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d18068 q = 2) : d173573 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18068, d173573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18068, d173573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18069 q = 2) : d173574 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18069, d173574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18069, d173574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d18070 q = 2) : d173575 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18070, d173575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18070, d173575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d18071 q = 2) : d173576 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18071, d173576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d18071, d173576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro16486 (p : Pattern) (selected : d18075 p = 2) : d18101 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18066 q = 2) : d18015 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18066, d18015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16484 q selected
    | true =>
      simp only [d18066, d18015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18067 q = 2) : d18016 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18067, d18016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18067, d18016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18072 q = 2) : d18098 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18072, d18098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18072, d18098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18073 q = 2) : d18099 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18073, d18099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18073, d18099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18074 q = 2) : d18100 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18074, d18100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18074, d18100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18075 q = 2) : d18101 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18075, d18101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18075, d18101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16487 (p : Pattern) (selected : d18078 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1391 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro846 q selected
  have h2 (q : Pattern) (selected : d1121 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro846 q selected
    | true =>
      simp only [d1121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1392 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17976 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17977 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18007 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d18078 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro16488 (p : Pattern) (selected : d18084 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d17980 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16469 q selected
    | true =>
      simp only [d17980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16471 q selected
  have h2 (q : Pattern) (selected : d17981 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17982 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17990 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16471 q selected
    | true =>
      simp only [d17990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16472 q selected
  have h5 (q : Pattern) (selected : d17991 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17992 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d17993 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d18079 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16471 q selected
    | true =>
      simp only [d18079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16487 q selected
  have h9 (q : Pattern) (selected : d18080 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d18081 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d18082 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d18082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d18083 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d18083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d18084 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d18084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro16489 (p : Pattern) (selected : d18090 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18085 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16488 q selected
    | true =>
      simp only [d18085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18086 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18087 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18088 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18089 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18090 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16490 (p : Pattern) (selected : d18096 p = 2) : d173582 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18021 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16475 q selected
    | true =>
      simp only [d18021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16478 q selected
  have h2 (q : Pattern) (selected : d18076 q = 2) : d173577 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18076, d173577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16485 q selected
    | true =>
      simp only [d18076, d173577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16486 q selected
  have h3 (q : Pattern) (selected : d18077 q = 2) : d173578 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18077, d173578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d18077, d173578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18091 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16489 q selected
    | true =>
      simp only [d18091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18092 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18093 q = 2) : d173579 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18093, d173579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18093, d173579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d18094 q = 2) : d173580 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18094, d173580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18094, d173580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d18095 q = 2) : d173581 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18095, d173581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18095, d173581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d18096 q = 2) : d173582 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18096, d173582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18096, d173582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro16491 (p : Pattern) (selected : d18101 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18015 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16477 q selected
    | true =>
      simp only [d18015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18016 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18098 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18099 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18100 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18101 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro16492 (p : Pattern) (selected : d18107 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18102 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16491 q selected
    | true =>
      simp only [d18102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d18103 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18104 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d18104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d18105 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d18106 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18107 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16493 (p : Pattern) (selected : d18113 p = 2) : d173588 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18097 q = 2) : d173583 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18097, d173583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18097, d173583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16490 q selected
  have h2 (q : Pattern) (selected : d18108 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16492 q selected
  have h3 (q : Pattern) (selected : d18109 q = 2) : d173584 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d18109, d173584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d18109, d173584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18110 q = 2) : d173585 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d18110, d173585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18110, d173585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18111 q = 2) : d173586 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d18111, d173586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18111, d173586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18112 q = 2) : d173587 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d18112, d173587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18112, d173587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d18113 q = 2) : d173588 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d18113, d173588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18113, d173588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro16494 (p : Pattern) (selected : d18119 p = 2) : d173594 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d18114 q = 2) : d173589 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d18114, d173589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18114, d173589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16493 q selected
  have h2 (q : Pattern) (selected : d18115 q = 2) : d173590 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d18115, d173590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18115, d173590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d18116 q = 2) : d173591 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d18116, d173591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18116, d173591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18117 q = 2) : d173592 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d18117, d173592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18117, d173592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d18118 q = 2) : d173593 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d18118, d173593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18118, d173593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d18119 q = 2) : d173594 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d18119, d173594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d18119, d173594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro16495 (p : Pattern) (selected : d18133 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1853 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro945 q selected
  have h2 (q : Pattern) (selected : d1665 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro945 q selected
    | true =>
      simp only [d1665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1854 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18123 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18124 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17004 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10596 q selected
  have h7 (q : Pattern) (selected : d10036 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10596 q selected
    | true =>
      simp only [d10036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d17005 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d18125 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d18125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d18126 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d18126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d18127 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d15380 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10597 q selected
  have h13 (q : Pattern) (selected : d10046 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10597 q selected
    | true =>
      simp only [d10046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15381 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d18128 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d18128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d18129 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d18129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d15387 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10599 q selected
  have h18 (q : Pattern) (selected : d10063 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10599 q selected
    | true =>
      simp only [d10063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d15388 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d15388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d18130 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d18130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d18131 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d18131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d18132 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d18132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d18133 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d18133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro16496 (p : Pattern) (selected : d18142 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1857 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro924 q selected
  have h2 (q : Pattern) (selected : d1555 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro924 q selected
    | true =>
      simp only [d1555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1858 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18134 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18135 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17011 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10601 q selected
  have h7 (q : Pattern) (selected : d10074 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10601 q selected
    | true =>
      simp only [d10074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d17012 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d18136 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d18136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d18137 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d18137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d18138 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d15387 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10599 q selected
  have h13 (q : Pattern) (selected : d10063 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10599 q selected
    | true =>
      simp only [d10063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15388 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d18130 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d18130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d18131 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d18131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d15397 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10602 q selected
  have h18 (q : Pattern) (selected : d10085 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10602 q selected
    | true =>
      simp only [d10085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d15398 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d15398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d18139 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d18139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d18140 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d18140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d18141 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d18141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d18142 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d18142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro16497 (p : Pattern) (selected : d18150 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d13486 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d13486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10604 q selected
  have h2 (q : Pattern) (selected : d10099 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10604 q selected
    | true =>
      simp only [d10099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d13487 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d13487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18146 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18147 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d15397 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10602 q selected
  have h7 (q : Pattern) (selected : d10085 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10602 q selected
    | true =>
      simp only [d10085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d15398 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d15398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d18139 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d18139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d18140 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d18140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d18148 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d18149 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d18149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d18150 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d18150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro16498 (p : Pattern) (selected : d18160 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1862 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro927 q selected
  have h2 (q : Pattern) (selected : d1570 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro927 q selected
    | true =>
      simp only [d1570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1863 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18155 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18156 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d17027 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10606 q selected
  have h7 (q : Pattern) (selected : d10115 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10606 q selected
    | true =>
      simp only [d10115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d17028 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d18157 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d18157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d18158 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d18158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d18159 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d15397 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10602 q selected
  have h13 (q : Pattern) (selected : d10085 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10602 q selected
    | true =>
      simp only [d10085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d15398 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d15398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d18139 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d18139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d18140 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d18140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d18149 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d18149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d18160 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d18160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro16499 (p : Pattern) (selected : d18170 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d6496 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3858 q selected
  have h2 (q : Pattern) (selected : d5134 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3858 q selected
    | true =>
      simp only [d5134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d6497 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d6497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d6497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d18164 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d18164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d18165 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d18165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d18166 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d18166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d15412 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d15412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10608 q selected
  have h8 (q : Pattern) (selected : d10135 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10608 q selected
    | true =>
      simp only [d10135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d15413 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d15413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d18167 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d18167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d18168 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d18168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d18169 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d18169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d18170 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d18170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
end NetHack.Soko22Hazard87
