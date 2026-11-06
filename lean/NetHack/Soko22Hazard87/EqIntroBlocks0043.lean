import NetHack.Soko22Hazard87.EqIntroBlocks0042
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro10750 (p : Pattern) (selected : d20126 p = 0) : d129979 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20110 q = 0) : d129967 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20110, d129967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20110, d129967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10747 q selected
  have h2 (q : Pattern) (selected : d20121 q = 0) : d129974 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20121, d129974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20121, d129974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10749 q selected
  have h3 (q : Pattern) (selected : d20122 q = 0) : d129975 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20122, d129975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20122, d129975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20123 q = 0) : d129976 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d20123, d129976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20123, d129976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20124 q = 0) : d129977 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d20124, d129977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20124, d129977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20125 q = 0) : d129978 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d20125, d129978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20125, d129978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20126 q = 0) : d129979 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d20126, d129979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20126, d129979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro10751 (p : Pattern) (selected : d20132 p = 0) : d129985 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20127 q = 0) : d129980 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d20127, d129980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20127, d129980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10750 q selected
  have h2 (q : Pattern) (selected : d20128 q = 0) : d129981 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d20128, d129981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20128, d129981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20129 q = 0) : d129982 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d20129, d129982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20129, d129982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20130 q = 0) : d129983 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d20130, d129983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20130, d129983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20131 q = 0) : d129984 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d20131, d129984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20131, d129984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20132 q = 0) : d129985 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d20132, d129985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20132, d129985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro10752 (p : Pattern) (selected : d20147 p = 0) : d130000 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10092 q = 0) : d101519 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10092, d101519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6715 q selected
    | true =>
      simp only [d10092, d101519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6718 q selected
  have h2 (q : Pattern) (selected : d20136 q = 0) : d129989 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20136, d129989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20136, d129989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20137 q = 0) : d129990 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20137, d129990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20137, d129990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10107 q = 0) : d101534 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10107, d101534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6718 q selected
    | true =>
      simp only [d10107, d101534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6720 q selected
  have h5 (q : Pattern) (selected : d20138 q = 0) : d129991 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20138, d129991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20138, d129991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20139 q = 0) : d129992 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20139, d129992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20139, d129992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d20140 q = 0) : d129993 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20140, d129993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20140, d129993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10122 q = 0) : d101549 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6718 q selected
    | true =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6722 q selected
  have h9 (q : Pattern) (selected : d20141 q = 0) : d129994 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20141, d129994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20141, d129994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d20142 q = 0) : d129995 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20142, d129995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20142, d129995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10142 q = 0) : d101569 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6722 q selected
    | true =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6724 q selected
  have h12 (q : Pattern) (selected : d20143 q = 0) : d129996 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20143, d129996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20143, d129996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d20144 q = 0) : d129997 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20144, d129997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20144, d129997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d20145 q = 0) : d129998 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20145, d129998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d20145, d129998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d20146 q = 0) : d129999 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20146, d129999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20146, d129999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d10093 q = 0) : d101520 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10093, d101520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10093, d101520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d10094 q = 0) : d101521 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10094, d101521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10094, d101521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d10108 q = 0) : d101535 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10108, d101535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10108, d101535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d10109 q = 0) : d101536 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10109, d101536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10109, d101536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d10110 q = 0) : d101537 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10110, d101537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d10110, d101537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d10123 q = 0) : d101550 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d10124 q = 0) : d101551 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d10143 q = 0) : d101570 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d10144 q = 0) : d101571 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d10145 q = 0) : d101572 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d10146 q = 0) : d101573 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10146, d101573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d10146, d101573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d20147 q = 0) : d130000 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20147, d130000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d20147, d130000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro10753 (p : Pattern) (selected : d20152 p = 0) : d130005 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10122 q = 0) : d101549 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6718 q selected
    | true =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6722 q selected
  have h2 (q : Pattern) (selected : d20141 q = 0) : d129994 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20141, d129994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20141, d129994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20142 q = 0) : d129995 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20142, d129995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20142, d129995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10142 q = 0) : d101569 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6722 q selected
    | true =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6724 q selected
  have h5 (q : Pattern) (selected : d20143 q = 0) : d129996 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20143, d129996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20143, d129996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20144 q = 0) : d129997 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20144, d129997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20144, d129997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d20145 q = 0) : d129998 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20145, d129998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20145, d129998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d20150 q = 0) : d130003 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20150, d130003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20150, d130003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d20151 q = 0) : d130004 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20151, d130004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20151, d130004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10123 q = 0) : d101550 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d10124 q = 0) : d101551 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d10143 q = 0) : d101570 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d10144 q = 0) : d101571 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d10145 q = 0) : d101572 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d10150 q = 0) : d101577 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10150, d101577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d10150, d101577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d10151 q = 0) : d101578 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10151, d101578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d10151, d101578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d20152 q = 0) : d130005 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20152, d130005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d20152, d130005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro10754 (p : Pattern) (selected : d20158 p = 0) : d130011 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20148 q = 0) : d130001 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20148, d130001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10752 q selected
    | true =>
      simp only [d20148, d130001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20149 q = 0) : d130002 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20149, d130002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20149, d130002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20153 q = 0) : d130006 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20153, d130006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10753 q selected
    | true =>
      simp only [d20153, d130006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20154 q = 0) : d130007 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20154, d130007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20154, d130007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20155 q = 0) : d130008 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20155, d130008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20155, d130008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20156 q = 0) : d130009 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20156, d130009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20156, d130009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20157 q = 0) : d130010 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20157, d130010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20157, d130010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d20158 q = 0) : d130011 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20158, d130011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20158, d130011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro10755 (p : Pattern) (selected : d20163 p = 0) : d130016 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10164 q = 0) : d101591 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10164, d101591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6722 q selected
    | true =>
      simp only [d10164, d101591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6728 q selected
  have h2 (q : Pattern) (selected : d20159 q = 0) : d130012 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20159, d130012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20159, d130012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20160 q = 0) : d130013 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20160, d130013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20160, d130013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20161 q = 0) : d130014 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20161, d130014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20161, d130014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20162 q = 0) : d130015 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20162, d130015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20162, d130015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10165 q = 0) : d101592 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10165, d101592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10165, d101592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10166 q = 0) : d101593 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10166, d101593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10166, d101593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10167 q = 0) : d101594 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10167, d101594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10167, d101594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10168 q = 0) : d101595 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10168, d101595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10168, d101595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d20163 q = 0) : d130016 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20163, d130016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20163, d130016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro10756 (p : Pattern) (selected : d20169 p = 0) : d130022 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20153 q = 0) : d130006 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20153, d130006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10753 q selected
    | true =>
      simp only [d20153, d130006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20154 q = 0) : d130007 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20154, d130007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20154, d130007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20164 q = 0) : d130017 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20164, d130017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10755 q selected
    | true =>
      simp only [d20164, d130017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20165 q = 0) : d130018 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20165, d130018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20165, d130018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20166 q = 0) : d130019 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20166, d130019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20166, d130019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20167 q = 0) : d130020 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20167, d130020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20167, d130020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20168 q = 0) : d130021 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20168, d130021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20168, d130021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d20169 q = 0) : d130022 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20169, d130022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20169, d130022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro10757 (p : Pattern) (selected : d20180 p = 0) : d130025 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10234 q = 0) : d101549 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10234, d101549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6736 q selected
    | true =>
      simp only [d10234, d101549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6738 q selected
  have h2 (q : Pattern) (selected : d20171 q = 0) : d129994 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20171, d129994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20171, d129994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20172 q = 0) : d129995 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20172, d129995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20172, d129995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10262 q = 0) : d101569 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10262, d101569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6738 q selected
    | true =>
      simp only [d10262, d101569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6741 q selected
  have h5 (q : Pattern) (selected : d20173 q = 0) : d129996 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20173, d129996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20173, d129996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20174 q = 0) : d129997 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20174, d129997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20174, d129997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d20175 q = 0) : d129998 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20175, d129998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20175, d129998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10271 q = 0) : d101591 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10271, d101591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6738 q selected
    | true =>
      simp only [d10271, d101591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6742 q selected
  have h9 (q : Pattern) (selected : d20176 q = 0) : d130012 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20176, d130012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20176, d130012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d20177 q = 0) : d130013 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20177, d130013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20177, d130013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d20178 q = 0) : d130014 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20178, d130014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d20178, d130014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d20179 q = 0) : d130024 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20179, d130024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20179, d130024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d10235 q = 0) : d101550 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10235, d101550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10235, d101550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d10236 q = 0) : d101551 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10236, d101551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10236, d101551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d10263 q = 0) : d101570 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10263, d101570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10263, d101570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d10264 q = 0) : d101571 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10264, d101571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10264, d101571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d10265 q = 0) : d101572 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10265, d101572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d10265, d101572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d10272 q = 0) : d101592 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10272, d101592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10272, d101592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d10273 q = 0) : d101593 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10273, d101593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10273, d101593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d10274 q = 0) : d101594 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10274, d101594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d10274, d101594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d10275 q = 0) : d101604 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10275, d101604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d10275, d101604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d20180 q = 0) : d130025 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20180, d130025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d20180, d130025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  exact h22 p selected
theorem eqIntro10758 (p : Pattern) (selected : d20184 p = 0) : d130016 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10271 q = 0) : d101591 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10271, d101591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6738 q selected
    | true =>
      simp only [d10271, d101591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6742 q selected
  have h2 (q : Pattern) (selected : d20176 q = 0) : d130012 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20176, d130012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20176, d130012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20177 q = 0) : d130013 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20177, d130013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20177, d130013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20178 q = 0) : d130014 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20178, d130014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20178, d130014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20183 q = 0) : d130015 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20183, d130015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20183, d130015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10272 q = 0) : d101592 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10272, d101592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10272, d101592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10273 q = 0) : d101593 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10273, d101593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10273, d101593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10274 q = 0) : d101594 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10274, d101594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10274, d101594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10279 q = 0) : d101595 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10279, d101595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10279, d101595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d20184 q = 0) : d130016 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20184, d130016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20184, d130016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro10759 (p : Pattern) (selected : d20190 p = 0) : d130031 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20181 q = 0) : d130026 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20181, d130026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10757 q selected
    | true =>
      simp only [d20181, d130026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20182 q = 0) : d130027 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20182, d130027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20182, d130027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20185 q = 0) : d130017 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20185, d130017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10758 q selected
    | true =>
      simp only [d20185, d130017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20186 q = 0) : d130018 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20186, d130018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20186, d130018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20187 q = 0) : d130028 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20187, d130028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20187, d130028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20188 q = 0) : d130029 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20188, d130029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20188, d130029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20189 q = 0) : d130030 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20189, d130030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20189, d130030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d20190 q = 0) : d130031 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20190, d130031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20190, d130031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro10760 (p : Pattern) (selected : d20194 p = 0) : d130035 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20185 q = 0) : d130017 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20185, d130017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10758 q selected
    | true =>
      simp only [d20185, d130017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20186 q = 0) : d130018 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20186, d130018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20186, d130018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20191 q = 0) : d130032 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20191, d130032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20191, d130032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20192 q = 0) : d130033 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20192, d130033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20192, d130033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20193 q = 0) : d130034 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20193, d130034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20193, d130034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20194 q = 0) : d130035 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20194, d130035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20194, d130035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10761 (p : Pattern) (selected : d20201 p = 0) : d130042 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10122 q = 0) : d101549 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6718 q selected
    | true =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6722 q selected
  have h2 (q : Pattern) (selected : d20141 q = 0) : d129994 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20141, d129994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20141, d129994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20142 q = 0) : d129995 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20142, d129995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20142, d129995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10142 q = 0) : d101569 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6722 q selected
    | true =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6724 q selected
  have h5 (q : Pattern) (selected : d20143 q = 0) : d129996 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20143, d129996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20143, d129996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20144 q = 0) : d129997 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20144, d129997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20144, d129997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d20145 q = 0) : d129998 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20145, d129998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20145, d129998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10294 q = 0) : d101619 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10294, d101619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6722 q selected
    | true =>
      simp only [d10294, d101619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6747 q selected
  have h9 (q : Pattern) (selected : d20197 q = 0) : d130038 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20197, d130038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20197, d130038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d20198 q = 0) : d130039 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20198, d130039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20198, d130039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d20199 q = 0) : d130040 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20199, d130040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d20199, d130040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d20200 q = 0) : d130041 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20200, d130041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20200, d130041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d10123 q = 0) : d101550 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d10124 q = 0) : d101551 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d10143 q = 0) : d101570 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d10144 q = 0) : d101571 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d10145 q = 0) : d101572 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d10295 q = 0) : d101620 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10295, d101620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10295, d101620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d10296 q = 0) : d101621 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10296, d101621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10296, d101621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d10297 q = 0) : d101622 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10297, d101622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d10297, d101622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d10298 q = 0) : d101623 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10298, d101623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d10298, d101623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d20201 q = 0) : d130042 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20201, d130042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d20201, d130042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  exact h22 p selected
theorem eqIntro10762 (p : Pattern) (selected : d20207 p = 0) : d130048 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20202 q = 0) : d130043 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20202, d130043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10761 q selected
    | true =>
      simp only [d20202, d130043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20203 q = 0) : d130044 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20203, d130044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20203, d130044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20204 q = 0) : d130045 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20204, d130045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20204, d130045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20205 q = 0) : d130046 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20205, d130046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20205, d130046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20206 q = 0) : d130047 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20206, d130047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20206, d130047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20207 q = 0) : d130048 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20207, d130048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20207, d130048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10763 (p : Pattern) (selected : d20213 p = 0) : d130054 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20170 q = 0) : d130023 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20170, d130023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10754 q selected
    | true =>
      simp only [d20170, d130023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10756 q selected
  have h2 (q : Pattern) (selected : d20195 q = 0) : d130036 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20195, d130036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10759 q selected
    | true =>
      simp only [d20195, d130036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10760 q selected
  have h3 (q : Pattern) (selected : d20196 q = 0) : d130037 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20196, d130037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20196, d130037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20208 q = 0) : d130049 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20208, d130049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10762 q selected
    | true =>
      simp only [d20208, d130049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20209 q = 0) : d130050 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20209, d130050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20209, d130050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20210 q = 0) : d130051 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20210, d130051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20210, d130051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d20211 q = 0) : d130052 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20211, d130052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20211, d130052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d20212 q = 0) : d130053 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20212, d130053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20212, d130053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d20213 q = 0) : d130054 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20213, d130054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20213, d130054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro10764 (p : Pattern) (selected : d20218 p = 0) : d130035 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20164 q = 0) : d130017 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20164, d130017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10755 q selected
    | true =>
      simp only [d20164, d130017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20165 q = 0) : d130018 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20165, d130018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20165, d130018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20215 q = 0) : d130032 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20215, d130032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20215, d130032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20216 q = 0) : d130033 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20216, d130033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20216, d130033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20217 q = 0) : d130034 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20217, d130034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20217, d130034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20218 q = 0) : d130035 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20218, d130035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20218, d130035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10765 (p : Pattern) (selected : d20224 p = 0) : d130061 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20219 q = 0) : d130056 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20219, d130056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10764 q selected
    | true =>
      simp only [d20219, d130056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20220 q = 0) : d130057 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20220, d130057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20220, d130057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20221 q = 0) : d130058 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20221, d130058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20221, d130058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20222 q = 0) : d130059 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20222, d130059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20222, d130059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20223 q = 0) : d130060 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20223, d130060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20223, d130060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20224 q = 0) : d130061 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20224, d130061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20224, d130061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro10766 (p : Pattern) (selected : d20230 p = 0) : d130067 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20214 q = 0) : d130055 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20214, d130055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20214, d130055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10763 q selected
  have h2 (q : Pattern) (selected : d20225 q = 0) : d130062 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20225, d130062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20225, d130062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10765 q selected
  have h3 (q : Pattern) (selected : d20226 q = 0) : d130063 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20226, d130063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20226, d130063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20227 q = 0) : d130064 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d20227, d130064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20227, d130064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20228 q = 0) : d130065 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d20228, d130065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20228, d130065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20229 q = 0) : d130066 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d20229, d130066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20229, d130066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20230 q = 0) : d130067 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d20230, d130067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20230, d130067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro10767 (p : Pattern) (selected : d20236 p = 0) : d130073 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20231 q = 0) : d130068 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d20231, d130068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20231, d130068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10766 q selected
  have h2 (q : Pattern) (selected : d20232 q = 0) : d130069 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d20232, d130069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20232, d130069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20233 q = 0) : d130070 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d20233, d130070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20233, d130070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20234 q = 0) : d130071 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d20234, d130071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20234, d130071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20235 q = 0) : d130072 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d20235, d130072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20235, d130072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20236 q = 0) : d130073 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d20236, d130073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20236, d130073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro10768 (p : Pattern) (selected : d20252 p = 0) : d130089 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10378 q = 0) : d101699 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10378, d101699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6757 q selected
    | true =>
      simp only [d10378, d101699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6760 q selected
  have h2 (q : Pattern) (selected : d20241 q = 0) : d130078 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20241, d130078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20241, d130078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20242 q = 0) : d130079 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20242, d130079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20242, d130079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10383 q = 0) : d101704 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10383, d101704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6760 q selected
    | true =>
      simp only [d10383, d101704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6761 q selected
  have h5 (q : Pattern) (selected : d20243 q = 0) : d130080 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20243, d130080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20243, d130080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20244 q = 0) : d130081 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20244, d130081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20244, d130081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d20245 q = 0) : d130082 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20245, d130082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20245, d130082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10398 q = 0) : d101719 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6760 q selected
    | true =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6763 q selected
  have h9 (q : Pattern) (selected : d20246 q = 0) : d130083 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20246, d130083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20246, d130083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d20247 q = 0) : d130084 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20247, d130084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20247, d130084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10419 q = 0) : d101740 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6763 q selected
    | true =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6765 q selected
  have h12 (q : Pattern) (selected : d20248 q = 0) : d130085 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20248, d130085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20248, d130085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d20249 q = 0) : d130086 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20249, d130086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20249, d130086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d20250 q = 0) : d130087 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20250, d130087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d20250, d130087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d20251 q = 0) : d130088 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20251, d130088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20251, d130088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d10379 q = 0) : d101700 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10379, d101700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10379, d101700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d10380 q = 0) : d101701 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10380, d101701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10380, d101701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d10384 q = 0) : d101705 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10384, d101705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10384, d101705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d10385 q = 0) : d101706 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10385, d101706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10385, d101706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d10386 q = 0) : d101707 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10386, d101707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d10386, d101707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  have h21 (q : Pattern) (selected : d10399 q = 0) : d101720 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d10400 q = 0) : d101721 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d10420 q = 0) : d101741 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d10421 q = 0) : d101742 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d10422 q = 0) : d101743 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d10423 q = 0) : d101744 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10423, d101744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d10423, d101744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d20252 q = 0) : d130089 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20252, d130089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d20252, d130089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro10769 (p : Pattern) (selected : d20257 p = 0) : d130094 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10398 q = 0) : d101719 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6760 q selected
    | true =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6763 q selected
  have h2 (q : Pattern) (selected : d20246 q = 0) : d130083 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20246, d130083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20246, d130083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20247 q = 0) : d130084 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20247, d130084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20247, d130084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10419 q = 0) : d101740 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6763 q selected
    | true =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6765 q selected
  have h5 (q : Pattern) (selected : d20248 q = 0) : d130085 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20248, d130085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20248, d130085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20249 q = 0) : d130086 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20249, d130086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20249, d130086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d20250 q = 0) : d130087 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20250, d130087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20250, d130087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d20255 q = 0) : d130092 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20255, d130092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20255, d130092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d20256 q = 0) : d130093 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20256, d130093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20256, d130093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10399 q = 0) : d101720 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d10400 q = 0) : d101721 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d10420 q = 0) : d101741 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d10421 q = 0) : d101742 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d10422 q = 0) : d101743 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d10427 q = 0) : d101748 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10427, d101748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d10427, d101748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d10428 q = 0) : d101749 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10428, d101749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d10428, d101749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d20257 q = 0) : d130094 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20257, d130094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d20257, d130094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro10770 (p : Pattern) (selected : d20263 p = 0) : d130100 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20253 q = 0) : d130090 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20253, d130090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10768 q selected
    | true =>
      simp only [d20253, d130090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20254 q = 0) : d130091 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20254, d130091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20254, d130091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20258 q = 0) : d130095 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20258, d130095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10769 q selected
    | true =>
      simp only [d20258, d130095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20259 q = 0) : d130096 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20259, d130096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20259, d130096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20260 q = 0) : d130097 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20260, d130097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20260, d130097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20261 q = 0) : d130098 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20261, d130098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20261, d130098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20262 q = 0) : d130099 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20262, d130099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20262, d130099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d20263 q = 0) : d130100 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20263, d130100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20263, d130100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro10771 (p : Pattern) (selected : d20268 p = 0) : d130105 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10441 q = 0) : d101762 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10441, d101762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6763 q selected
    | true =>
      simp only [d10441, d101762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6769 q selected
  have h2 (q : Pattern) (selected : d20264 q = 0) : d130101 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20264, d130101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20264, d130101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20265 q = 0) : d130102 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20265, d130102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20265, d130102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20266 q = 0) : d130103 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20266, d130103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20266, d130103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20267 q = 0) : d130104 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20267, d130104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20267, d130104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10442 q = 0) : d101763 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10442, d101763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10442, d101763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10443 q = 0) : d101764 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10443, d101764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10443, d101764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10444 q = 0) : d101765 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10444, d101765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10444, d101765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10445 q = 0) : d101766 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10445, d101766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10445, d101766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d20268 q = 0) : d130105 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20268, d130105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20268, d130105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro10772 (p : Pattern) (selected : d20274 p = 0) : d130111 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20258 q = 0) : d130095 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20258, d130095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10769 q selected
    | true =>
      simp only [d20258, d130095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20259 q = 0) : d130096 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20259, d130096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20259, d130096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20269 q = 0) : d130106 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20269, d130106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10771 q selected
    | true =>
      simp only [d20269, d130106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20270 q = 0) : d130107 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20270, d130107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20270, d130107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20271 q = 0) : d130108 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20271, d130108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20271, d130108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20272 q = 0) : d130109 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20272, d130109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20272, d130109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20273 q = 0) : d130110 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20273, d130110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20273, d130110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d20274 q = 0) : d130111 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20274, d130111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20274, d130111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro10773 (p : Pattern) (selected : d20285 p = 0) : d130114 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10501 q = 0) : d101719 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10501, d101719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6775 q selected
    | true =>
      simp only [d10501, d101719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6777 q selected
  have h2 (q : Pattern) (selected : d20276 q = 0) : d130083 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20276, d130083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20276, d130083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20277 q = 0) : d130084 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20277, d130084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20277, d130084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10528 q = 0) : d101740 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10528, d101740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6777 q selected
    | true =>
      simp only [d10528, d101740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6780 q selected
  have h5 (q : Pattern) (selected : d20278 q = 0) : d130085 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20278, d130085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20278, d130085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20279 q = 0) : d130086 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20279, d130086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20279, d130086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d20280 q = 0) : d130087 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20280, d130087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20280, d130087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10537 q = 0) : d101762 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10537, d101762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6777 q selected
    | true =>
      simp only [d10537, d101762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6781 q selected
  have h9 (q : Pattern) (selected : d20281 q = 0) : d130101 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20281, d130101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20281, d130101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d20282 q = 0) : d130102 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20282, d130102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20282, d130102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d20283 q = 0) : d130103 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20283, d130103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d20283, d130103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d20284 q = 0) : d130113 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20284, d130113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20284, d130113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d10502 q = 0) : d101720 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10502, d101720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10502, d101720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d10503 q = 0) : d101721 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10503, d101721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10503, d101721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d10529 q = 0) : d101741 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10529, d101741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10529, d101741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d10530 q = 0) : d101742 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10530, d101742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10530, d101742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d10531 q = 0) : d101743 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10531, d101743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d10531, d101743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d10538 q = 0) : d101763 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10538, d101763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10538, d101763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d10539 q = 0) : d101764 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10539, d101764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10539, d101764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d10540 q = 0) : d101765 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10540, d101765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d10540, d101765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d10541 q = 0) : d101775 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10541, d101775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d10541, d101775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d20285 q = 0) : d130114 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20285, d130114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d20285, d130114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  exact h22 p selected
theorem eqIntro10774 (p : Pattern) (selected : d20289 p = 0) : d130105 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10537 q = 0) : d101762 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10537, d101762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6777 q selected
    | true =>
      simp only [d10537, d101762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6781 q selected
  have h2 (q : Pattern) (selected : d20281 q = 0) : d130101 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20281, d130101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20281, d130101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20282 q = 0) : d130102 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20282, d130102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20282, d130102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20283 q = 0) : d130103 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20283, d130103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20283, d130103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20288 q = 0) : d130104 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20288, d130104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20288, d130104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10538 q = 0) : d101763 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10538, d101763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10538, d101763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10539 q = 0) : d101764 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10539, d101764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10539, d101764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10540 q = 0) : d101765 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10540, d101765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10540, d101765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10545 q = 0) : d101766 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10545, d101766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10545, d101766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d20289 q = 0) : d130105 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20289, d130105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20289, d130105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro10775 (p : Pattern) (selected : d20295 p = 0) : d130120 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20286 q = 0) : d130115 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20286, d130115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10773 q selected
    | true =>
      simp only [d20286, d130115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20287 q = 0) : d130116 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20287, d130116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20287, d130116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20290 q = 0) : d130106 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20290, d130106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10774 q selected
    | true =>
      simp only [d20290, d130106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20291 q = 0) : d130107 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20291, d130107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20291, d130107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20292 q = 0) : d130117 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20292, d130117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20292, d130117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20293 q = 0) : d130118 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20293, d130118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20293, d130118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20294 q = 0) : d130119 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20294, d130119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20294, d130119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d20295 q = 0) : d130120 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20295, d130120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20295, d130120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro10776 (p : Pattern) (selected : d20299 p = 0) : d130124 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20290 q = 0) : d130106 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20290, d130106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10774 q selected
    | true =>
      simp only [d20290, d130106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20291 q = 0) : d130107 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20291, d130107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20291, d130107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20296 q = 0) : d130121 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20296, d130121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20296, d130121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20297 q = 0) : d130122 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20297, d130122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20297, d130122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20298 q = 0) : d130123 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20298, d130123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20298, d130123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20299 q = 0) : d130124 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20299, d130124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20299, d130124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10777 (p : Pattern) (selected : d20306 p = 0) : d130131 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10398 q = 0) : d101719 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6760 q selected
    | true =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6763 q selected
  have h2 (q : Pattern) (selected : d20246 q = 0) : d130083 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20246, d130083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20246, d130083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20247 q = 0) : d130084 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20247, d130084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20247, d130084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10419 q = 0) : d101740 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6763 q selected
    | true =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6765 q selected
  have h5 (q : Pattern) (selected : d20248 q = 0) : d130085 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20248, d130085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20248, d130085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20249 q = 0) : d130086 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20249, d130086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20249, d130086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d20250 q = 0) : d130087 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20250, d130087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20250, d130087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10560 q = 0) : d101790 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10560, d101790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6763 q selected
    | true =>
      simp only [d10560, d101790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6786 q selected
  have h9 (q : Pattern) (selected : d20302 q = 0) : d130127 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20302, d130127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20302, d130127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d20303 q = 0) : d130128 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20303, d130128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20303, d130128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d20304 q = 0) : d130129 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20304, d130129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d20304, d130129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d20305 q = 0) : d130130 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20305, d130130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20305, d130130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d10399 q = 0) : d101720 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d10400 q = 0) : d101721 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d10420 q = 0) : d101741 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d10421 q = 0) : d101742 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d10422 q = 0) : d101743 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d10561 q = 0) : d101791 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10561, d101791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10561, d101791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d10562 q = 0) : d101792 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10562, d101792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10562, d101792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d10563 q = 0) : d101793 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10563, d101793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d10563, d101793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d10564 q = 0) : d101794 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10564, d101794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d10564, d101794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d20306 q = 0) : d130131 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20306, d130131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d20306, d130131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  exact h22 p selected
theorem eqIntro10778 (p : Pattern) (selected : d20312 p = 0) : d130137 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20307 q = 0) : d130132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20307, d130132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10777 q selected
    | true =>
      simp only [d20307, d130132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20308 q = 0) : d130133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20308, d130133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20308, d130133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20309 q = 0) : d130134 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20309, d130134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20309, d130134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20310 q = 0) : d130135 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20310, d130135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20310, d130135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20311 q = 0) : d130136 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20311, d130136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20311, d130136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20312 q = 0) : d130137 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20312, d130137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20312, d130137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10779 (p : Pattern) (selected : d20318 p = 0) : d130143 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20275 q = 0) : d130112 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20275, d130112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10770 q selected
    | true =>
      simp only [d20275, d130112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10772 q selected
  have h2 (q : Pattern) (selected : d20300 q = 0) : d130125 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20300, d130125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10775 q selected
    | true =>
      simp only [d20300, d130125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10776 q selected
  have h3 (q : Pattern) (selected : d20301 q = 0) : d130126 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20301, d130126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20301, d130126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20313 q = 0) : d130138 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20313, d130138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10778 q selected
    | true =>
      simp only [d20313, d130138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20314 q = 0) : d130139 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20314, d130139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20314, d130139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20315 q = 0) : d130140 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20315, d130140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20315, d130140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d20316 q = 0) : d130141 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20316, d130141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20316, d130141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d20317 q = 0) : d130142 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20317, d130142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20317, d130142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d20318 q = 0) : d130143 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20318, d130143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20318, d130143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro10780 (p : Pattern) (selected : d20323 p = 0) : d130124 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20269 q = 0) : d130106 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20269, d130106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10771 q selected
    | true =>
      simp only [d20269, d130106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20270 q = 0) : d130107 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20270, d130107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20270, d130107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20320 q = 0) : d130121 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20320, d130121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20320, d130121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20321 q = 0) : d130122 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20321, d130122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20321, d130122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20322 q = 0) : d130123 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20322, d130123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20322, d130123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20323 q = 0) : d130124 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20323, d130124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20323, d130124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10781 (p : Pattern) (selected : d20329 p = 0) : d130150 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20324 q = 0) : d130145 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20324, d130145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10780 q selected
    | true =>
      simp only [d20324, d130145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20325 q = 0) : d130146 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20325, d130146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20325, d130146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20326 q = 0) : d130147 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20326, d130147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20326, d130147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20327 q = 0) : d130148 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20327, d130148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20327, d130148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20328 q = 0) : d130149 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20328, d130149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20328, d130149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20329 q = 0) : d130150 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20329, d130150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20329, d130150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro10782 (p : Pattern) (selected : d20335 p = 0) : d130156 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20319 q = 0) : d130144 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20319, d130144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20319, d130144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10779 q selected
  have h2 (q : Pattern) (selected : d20330 q = 0) : d130151 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20330, d130151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20330, d130151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10781 q selected
  have h3 (q : Pattern) (selected : d20331 q = 0) : d130152 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20331, d130152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20331, d130152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20332 q = 0) : d130153 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d20332, d130153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20332, d130153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20333 q = 0) : d130154 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d20333, d130154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20333, d130154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20334 q = 0) : d130155 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d20334, d130155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20334, d130155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20335 q = 0) : d130156 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d20335, d130156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20335, d130156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro10783 (p : Pattern) (selected : d20341 p = 0) : d130162 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20336 q = 0) : d130157 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d20336, d130157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20336, d130157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10782 q selected
  have h2 (q : Pattern) (selected : d20337 q = 0) : d130158 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d20337, d130158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20337, d130158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20338 q = 0) : d130159 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d20338, d130159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20338, d130159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20339 q = 0) : d130160 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d20339, d130160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20339, d130160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20340 q = 0) : d130161 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d20340, d130161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20340, d130161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20341 q = 0) : d130162 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d20341, d130162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20341, d130162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro10784 (p : Pattern) (selected : d20347 p = 0) : d130168 p = 1 := by
  have h0 (q : Pattern) (selected : d19940 q = 0) : d129831 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d19940, d129831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10705 q selected
    | true =>
      simp only [d19940, d129831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10720 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d20030 q = 0) : d129899 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d20030, d129899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20030, d129899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10735 q selected
  have h3 (q : Pattern) (selected : d20031 q = 0) : d129900 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d20031, d129900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20031, d129900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20133 q = 0) : d129986 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d20133, d129986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20133, d129986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10751 q selected
  have h5 (q : Pattern) (selected : d20134 q = 0) : d129987 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d20134, d129987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20134, d129987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20135 q = 0) : d129988 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d20135, d129988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20135, d129988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d20237 q = 0) : d130074 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d20237, d130074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20237, d130074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10767 q selected
  have h8 (q : Pattern) (selected : d20238 q = 0) : d130075 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d20238, d130075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20238, d130075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d20239 q = 0) : d130076 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d20239, d130076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20239, d130076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d20240 q = 0) : d130077 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d20240, d130077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20240, d130077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d20342 q = 0) : d130163 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d20342, d130163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20342, d130163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10783 q selected
  have h12 (q : Pattern) (selected : d20343 q = 0) : d130164 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d20343, d130164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20343, d130164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d20344 q = 0) : d130165 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d20344, d130165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20344, d130165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d20345 q = 0) : d130166 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d20345, d130166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20345, d130166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d20346 q = 0) : d130167 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d20346, d130167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d20346, d130167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d20347 q = 0) : d130168 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d20347, d130168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d20347, d130168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro10785 (p : Pattern) (selected : d20353 p = 0) : d130174 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20348 q = 0) : d130169 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d20348, d130169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10784 q selected
    | true =>
      simp only [d20348, d130169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20349 q = 0) : d130170 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d20349, d130170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20349, d130170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d20350 q = 0) : d130171 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d20350, d130171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20350, d130171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20351 q = 0) : d130172 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d20351, d130172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20351, d130172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20352 q = 0) : d130173 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d20352, d130173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20352, d130173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20353 q = 0) : d130174 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d20353, d130174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20353, d130174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10786 (p : Pattern) (selected : d20359 p = 0) : d130180 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20354 q = 0) : d130175 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d20354, d130175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10785 q selected
    | true =>
      simp only [d20354, d130175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20355 q = 0) : d130176 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d20355, d130176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20355, d130176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d20356 q = 0) : d130177 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d20356, d130177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20356, d130177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20357 q = 0) : d130178 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d20357, d130178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20357, d130178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20358 q = 0) : d130179 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d20358, d130179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20358, d130179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20359 q = 0) : d130180 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d20359, d130180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20359, d130180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10787 (p : Pattern) (selected : d20365 p = 0) : d130186 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20360 q = 0) : d130181 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d20360, d130181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10786 q selected
    | true =>
      simp only [d20360, d130181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20361 q = 0) : d130182 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d20361, d130182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20361, d130182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d20362 q = 0) : d130183 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d20362, d130183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20362, d130183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20363 q = 0) : d130184 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d20363, d130184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20363, d130184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20364 q = 0) : d130185 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d20364, d130185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20364, d130185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20365 q = 0) : d130186 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d20365, d130186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20365, d130186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10788 (p : Pattern) (selected : d20371 p = 0) : d130192 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20366 q = 0) : d130187 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d20366, d130187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10787 q selected
    | true =>
      simp only [d20366, d130187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20367 q = 0) : d130188 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d20367, d130188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20367, d130188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d20368 q = 0) : d130189 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d20368, d130189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20368, d130189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20369 q = 0) : d130190 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d20369, d130190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20369, d130190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20370 q = 0) : d130191 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d20370, d130191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20370, d130191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20371 q = 0) : d130192 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d20371, d130192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20371, d130192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10789 (p : Pattern) (selected : d20377 p = 0) : d130198 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20372 q = 0) : d130193 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d20372, d130193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10788 q selected
    | true =>
      simp only [d20372, d130193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20373 q = 0) : d130194 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d20373, d130194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20373, d130194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d20374 q = 0) : d130195 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d20374, d130195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20374, d130195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20375 q = 0) : d130196 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d20375, d130196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20375, d130196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20376 q = 0) : d130197 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d20376, d130197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20376, d130197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20377 q = 0) : d130198 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d20377, d130198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20377, d130198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10790 (p : Pattern) (selected : d20383 p = 0) : d130204 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20378 q = 0) : d130199 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d20378, d130199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10789 q selected
    | true =>
      simp only [d20378, d130199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20379 q = 0) : d130200 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d20379, d130200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20379, d130200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d20380 q = 0) : d130201 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d20380, d130201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20380, d130201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20381 q = 0) : d130202 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d20381, d130202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20381, d130202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20382 q = 0) : d130203 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d20382, d130203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20382, d130203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20383 q = 0) : d130204 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d20383, d130204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20383, d130204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10791 (p : Pattern) (selected : d20389 p = 0) : d130210 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20384 q = 0) : d130205 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d20384, d130205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10790 q selected
    | true =>
      simp only [d20384, d130205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20385 q = 0) : d130206 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d20385, d130206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20385, d130206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d20386 q = 0) : d130207 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d20386, d130207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20386, d130207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20387 q = 0) : d130208 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d20387, d130208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20387, d130208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20388 q = 0) : d130209 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d20388, d130209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20388, d130209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20389 q = 0) : d130210 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d20389, d130210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20389, d130210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10792 (p : Pattern) (selected : d19781 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d9348 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6802 q selected
    | true =>
      simp only [d9348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d19777 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d19778 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d19779 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d19779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d19780 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d19780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9349 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9350 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d9351 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d9351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d9352 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d19781 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d19781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro10793 (p : Pattern) (selected : d19787 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d19782 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10792 q selected
    | true =>
      simp only [d19782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d19783 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d19784 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d19784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d19785 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d19785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d19786 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d19786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d19787 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d19787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10794 (p : Pattern) (selected : d19793 p = 1) : d130215 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d19776 q = 1) : d19776 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d19788 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10793 q selected
    | true =>
      simp only [d19788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d19789 q = 1) : d130211 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19789, d130211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d19789, d130211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d19750 q = 1) : d19750 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d19790 q = 1) : d130212 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d19790, d130212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d19790, d130212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d19791 q = 1) : d130213 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d19791, d130213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19791, d130213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d19792 q = 1) : d130214 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d19792, d130214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19792, d130214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d19793 q = 1) : d130215 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d19793, d130215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19793, d130215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro10795 (p : Pattern) (selected : d19799 p = 1) : d130221 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d19794 q = 1) : d130216 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d19794, d130216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19794, d130216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10794 q selected
  have h2 (q : Pattern) (selected : d19795 q = 1) : d130217 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d19795, d130217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d19795, d130217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d19796 q = 1) : d130218 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d19796, d130218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d19796, d130218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d19797 q = 1) : d130219 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d19797, d130219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d19797, d130219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d19798 q = 1) : d130220 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d19798, d130220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d19798, d130220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d19799 q = 1) : d130221 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d19799, d130221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19799, d130221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro10796 (p : Pattern) (selected : d19821 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d9407 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6807 q selected
    | true =>
      simp only [d9407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6802 q selected
  have h2 (q : Pattern) (selected : d19817 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d19818 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9348 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6802 q selected
    | true =>
      simp only [d9348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d19777 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d19778 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d19819 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d19819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d19779 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d19779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d19820 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d19820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d9408 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d9409 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d9349 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d9350 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d9410 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d9410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d9351 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d9351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d9411 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d9411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d19821 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d19821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro10797 (p : Pattern) (selected : d19827 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d19822 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10796 q selected
    | true =>
      simp only [d19822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d19823 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d19782 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10792 q selected
    | true =>
      simp only [d19782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d19783 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d19824 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d19824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d19825 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d19825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d19826 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d19826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d19827 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d19827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro10798 (p : Pattern) (selected : d19839 p = 1) : d130231 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d19816 q = 1) : d19816 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d19828 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10797 q selected
    | true =>
      simp only [d19828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10793 q selected
  have h3 (q : Pattern) (selected : d19829 q = 1) : d130227 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19829, d130227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d19829, d130227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d19835 q = 1) : d19835 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d19836 q = 1) : d130228 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d19836, d130228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d19836, d130228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d19837 q = 1) : d130229 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d19837, d130229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19837, d130229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d19838 q = 1) : d130230 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d19838, d130230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19838, d130230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d19839 q = 1) : d130231 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d19839, d130231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19839, d130231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro10799 (p : Pattern) (selected : d19851 p = 1) : d130237 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d19840 q = 1) : d130232 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d19840, d130232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19840, d130232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10798 q selected
  have h2 (q : Pattern) (selected : d19846 q = 1) : d19846 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d19847 q = 1) : d130233 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d19847, d130233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d19847, d130233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d19848 q = 1) : d130234 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d19848, d130234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d19848, d130234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d19849 q = 1) : d130235 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d19849, d130235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d19849, d130235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d19850 q = 1) : d130236 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d19850, d130236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d19850, d130236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d19851 q = 1) : d130237 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d19851, d130237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19851, d130237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro10800 (p : Pattern) (selected : d19857 p = 1) : d130243 p = 1 := by
  have h0 (q : Pattern) (selected : d19764 q = 1) : d19764 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d19800 q = 1) : d130222 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d19800, d130222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d19800, d130222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10795 q selected
  have h3 (q : Pattern) (selected : d19801 q = 1) : d130223 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d19801, d130223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d19801, d130223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d19802 q = 1) : d130224 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d19802, d130224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d19802, d130224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d19803 q = 1) : d130225 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d19803, d130225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d19803, d130225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d19804 q = 1) : d130226 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d19804, d130226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19804, d130226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d19852 q = 1) : d130238 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d19852, d130238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d19852, d130238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10799 q selected
  have h8 (q : Pattern) (selected : d19853 q = 1) : d130239 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d19853, d130239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d19853, d130239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d19854 q = 1) : d130240 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d19854, d130240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d19854, d130240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d19855 q = 1) : d130241 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d19855, d130241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d19855, d130241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d19856 q = 1) : d130242 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d19856, d130242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d19856, d130242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d19857 q = 1) : d130243 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d19857, d130243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d19857, d130243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro10801 (p : Pattern) (selected : d19890 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d9519 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6814 q selected
    | true =>
      simp only [d9519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6807 q selected
  have h2 (q : Pattern) (selected : d19885 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d19886 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9407 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6807 q selected
    | true =>
      simp only [d9407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6802 q selected
  have h5 (q : Pattern) (selected : d19817 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d19818 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d19887 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d19887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d19888 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d19888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d19889 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d19889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d9520 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d9521 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d9408 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d9409 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d9522 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d9522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d9523 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d9523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d9524 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d9524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d19890 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d19890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro10802 (p : Pattern) (selected : d19894 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d9407 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6807 q selected
    | true =>
      simp only [d9407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6802 q selected
  have h2 (q : Pattern) (selected : d19817 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d19818 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d19888 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d19888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d19893 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d19893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9408 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9409 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d9523 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d9523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d9528 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d19894 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d19894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro10803 (p : Pattern) (selected : d19900 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d19891 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10801 q selected
    | true =>
      simp only [d19891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d19892 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d19895 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10802 q selected
    | true =>
      simp only [d19895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d19896 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d19897 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d19897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d19898 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d19898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d19899 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d19899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d19900 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d19900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro10804 (p : Pattern) (selected : d19904 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d19895 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10802 q selected
    | true =>
      simp only [d19895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d19896 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d19901 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d19901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d19902 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d19902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d19903 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d19903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d19904 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d19904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10805 (p : Pattern) (selected : d19916 p = 1) : d130248 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d19884 q = 1) : d19884 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d19905 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10803 q selected
    | true =>
      simp only [d19905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10804 q selected
  have h3 (q : Pattern) (selected : d19906 q = 1) : d130244 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19906, d130244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d19906, d130244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d19912 q = 1) : d19912 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d19913 q = 1) : d130245 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d19913, d130245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d19913, d130245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d19914 q = 1) : d130246 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d19914, d130246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19914, d130246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d19915 q = 1) : d130247 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d19915, d130247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19915, d130247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d19916 q = 1) : d130248 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d19916, d130248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19916, d130248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro10806 (p : Pattern) (selected : d19933 p = 1) : d130254 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d19917 q = 1) : d130249 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d19917, d130249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19917, d130249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10805 q selected
  have h2 (q : Pattern) (selected : d19928 q = 1) : d19928 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d19929 q = 1) : d130250 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d19929, d130250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d19929, d130250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d19930 q = 1) : d130251 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d19930, d130251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d19930, d130251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d19931 q = 1) : d130252 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d19931, d130252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d19931, d130252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d19932 q = 1) : d130253 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d19932, d130253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d19932, d130253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d19933 q = 1) : d130254 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d19933, d130254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19933, d130254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro10807 (p : Pattern) (selected : d19939 p = 1) : d130260 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d19934 q = 1) : d130255 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d19934, d130255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19934, d130255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10806 q selected
  have h2 (q : Pattern) (selected : d19935 q = 1) : d130256 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d19935, d130256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19935, d130256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d19936 q = 1) : d130257 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d19936, d130257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19936, d130257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d19937 q = 1) : d130258 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d19937, d130258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19937, d130258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d19938 q = 1) : d130259 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d19938, d130259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19938, d130259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d19939 q = 1) : d130260 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d19939, d130260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19939, d130260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro10808 (p : Pattern) (selected : d19980 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d9684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6825 q selected
    | true =>
      simp only [d9684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6826 q selected
  have h2 (q : Pattern) (selected : d19973 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d19974 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9688 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6826 q selected
    | true =>
      simp only [d9688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6827 q selected
  have h5 (q : Pattern) (selected : d19975 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d19976 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d19977 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d19977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d19978 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d19978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d19979 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d19979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d9685 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d9686 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d9689 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d9690 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d9691 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d9691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d9692 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d9692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d9693 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d9693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d19980 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d19980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro10809 (p : Pattern) (selected : d19984 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d9688 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6826 q selected
    | true =>
      simp only [d9688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6827 q selected
  have h2 (q : Pattern) (selected : d19975 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d19976 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d19978 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d19978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d19983 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d19983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9689 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9690 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d9692 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d9692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d9697 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d19984 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d19984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro10810 (p : Pattern) (selected : d19990 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d19981 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10808 q selected
    | true =>
      simp only [d19981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d19982 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d19985 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10809 q selected
    | true =>
      simp only [d19985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d19986 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d19987 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d19987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d19988 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d19988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d19989 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d19989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d19990 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d19990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro10811 (p : Pattern) (selected : d19994 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d19985 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10809 q selected
    | true =>
      simp only [d19985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d19986 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d19986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d19991 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d19991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d19992 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d19992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d19993 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d19993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d19994 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d19994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10812 (p : Pattern) (selected : d20006 p = 1) : d130266 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d19972 q = 1) : d19972 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d19995 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10810 q selected
    | true =>
      simp only [d19995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10811 q selected
  have h3 (q : Pattern) (selected : d19996 q = 1) : d130262 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19996, d130262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d19996, d130262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20002 q = 1) : d20002 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d20003 q = 1) : d130263 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20003, d130263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20003, d130263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20004 q = 1) : d130264 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20004, d130264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20004, d130264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d20005 q = 1) : d130265 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20005, d130265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20005, d130265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d20006 q = 1) : d130266 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20006, d130266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20006, d130266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro10813 (p : Pattern) (selected : d20023 p = 1) : d130272 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20007 q = 1) : d130267 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20007, d130267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20007, d130267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10812 q selected
  have h2 (q : Pattern) (selected : d20018 q = 1) : d20018 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d20019 q = 1) : d130268 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20019, d130268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20019, d130268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20020 q = 1) : d130269 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d20020, d130269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20020, d130269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20021 q = 1) : d130270 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d20021, d130270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20021, d130270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20022 q = 1) : d130271 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d20022, d130271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20022, d130271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20023 q = 1) : d130272 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d20023, d130272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20023, d130272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro10814 (p : Pattern) (selected : d20029 p = 1) : d130278 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20024 q = 1) : d130273 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d20024, d130273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20024, d130273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10813 q selected
  have h2 (q : Pattern) (selected : d20025 q = 1) : d130274 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d20025, d130274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20025, d130274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20026 q = 1) : d130275 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d20026, d130275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20026, d130275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20027 q = 1) : d130276 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d20027, d130276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20027, d130276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20028 q = 1) : d130277 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d20028, d130277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20028, d130277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20029 q = 1) : d130278 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d20029, d130278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20029, d130278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro10815 (p : Pattern) (selected : d20076 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d9934 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6840 q selected
    | true =>
      simp only [d9934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6841 q selected
  have h2 (q : Pattern) (selected : d20067 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20068 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d9959 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6841 q selected
    | true =>
      simp only [d9959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6844 q selected
  have h5 (q : Pattern) (selected : d20069 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20070 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d20071 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d9965 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6841 q selected
    | true =>
      simp only [d9965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6845 q selected
  have h9 (q : Pattern) (selected : d20072 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d20073 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d20074 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d20074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d20075 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d9935 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d9936 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d9960 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d9960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d9961 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d9962 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d9962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d9966 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d9967 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d9968 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d9968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d9969 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d9969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d20076 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d20076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  exact h22 p selected
theorem eqIntro10816 (p : Pattern) (selected : d20080 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d9965 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6841 q selected
    | true =>
      simp only [d9965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6845 q selected
  have h2 (q : Pattern) (selected : d20072 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20073 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20074 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20079 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9966 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d9966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9967 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d9968 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d9968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d9973 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d20080 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro10817 (p : Pattern) (selected : d20086 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20077 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10815 q selected
    | true =>
      simp only [d20077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20078 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20081 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10816 q selected
    | true =>
      simp only [d20081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20082 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20083 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20084 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20085 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d20086 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro10818 (p : Pattern) (selected : d20090 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20081 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10816 q selected
    | true =>
      simp only [d20081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20082 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20087 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20088 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20089 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20090 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10819 (p : Pattern) (selected : d20109 p = 1) : d130285 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20066 q = 1) : d20066 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d20091 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10817 q selected
    | true =>
      simp only [d20091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10818 q selected
  have h3 (q : Pattern) (selected : d20092 q = 1) : d130281 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20092, d130281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20092, d130281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20105 q = 1) : d20105 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d20106 q = 1) : d130282 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20106, d130282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20106, d130282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20107 q = 1) : d130283 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20107, d130283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20107, d130283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d20108 q = 1) : d130284 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20108, d130284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20108, d130284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d20109 q = 1) : d130285 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20109, d130285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20109, d130285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro10820 (p : Pattern) (selected : d20126 p = 1) : d130291 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20110 q = 1) : d130286 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20110, d130286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20110, d130286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10819 q selected
  have h2 (q : Pattern) (selected : d20121 q = 1) : d20121 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d20122 q = 1) : d130287 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20122, d130287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20122, d130287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20123 q = 1) : d130288 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d20123, d130288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20123, d130288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20124 q = 1) : d130289 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d20124, d130289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20124, d130289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20125 q = 1) : d130290 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d20125, d130290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20125, d130290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20126 q = 1) : d130291 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d20126, d130291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20126, d130291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro10821 (p : Pattern) (selected : d20132 p = 1) : d130297 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20127 q = 1) : d130292 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d20127, d130292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20127, d130292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10820 q selected
  have h2 (q : Pattern) (selected : d20128 q = 1) : d130293 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d20128, d130293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20128, d130293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20129 q = 1) : d130294 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d20129, d130294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20129, d130294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20130 q = 1) : d130295 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d20130, d130295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20130, d130295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20131 q = 1) : d130296 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d20131, d130296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20131, d130296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20132 q = 1) : d130297 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d20132, d130297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20132, d130297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro10822 (p : Pattern) (selected : d20180 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10234 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6858 q selected
    | true =>
      simp only [d10234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6860 q selected
  have h2 (q : Pattern) (selected : d20171 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20172 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10262 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6860 q selected
    | true =>
      simp only [d10262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6863 q selected
  have h5 (q : Pattern) (selected : d20173 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20174 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d20175 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10271 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6860 q selected
    | true =>
      simp only [d10271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6864 q selected
  have h9 (q : Pattern) (selected : d20176 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d20177 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d20178 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d20178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d20179 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d10235 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d10236 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d10263 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d10264 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d10265 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d10265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d10272 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d10273 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d10274 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d10274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d10275 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d10275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d20180 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d20180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  exact h22 p selected
theorem eqIntro10823 (p : Pattern) (selected : d20184 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10271 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6860 q selected
    | true =>
      simp only [d10271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6864 q selected
  have h2 (q : Pattern) (selected : d20176 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20177 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20178 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20183 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10272 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10273 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10274 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10279 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d20184 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro10824 (p : Pattern) (selected : d20190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20181 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10822 q selected
    | true =>
      simp only [d20181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20182 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20185 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10823 q selected
    | true =>
      simp only [d20185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20186 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20187 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20188 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20189 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d20190 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro10825 (p : Pattern) (selected : d20194 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20185 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10823 q selected
    | true =>
      simp only [d20185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20186 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20191 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20192 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20193 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20194 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10826 (p : Pattern) (selected : d20213 p = 1) : d130305 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20170 q = 1) : d20170 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d20195 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10824 q selected
    | true =>
      simp only [d20195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10825 q selected
  have h3 (q : Pattern) (selected : d20196 q = 1) : d130301 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20196, d130301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20196, d130301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20209 q = 1) : d20209 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d20210 q = 1) : d130302 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20210, d130302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20210, d130302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20211 q = 1) : d130303 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20211, d130303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20211, d130303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d20212 q = 1) : d130304 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20212, d130304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20212, d130304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d20213 q = 1) : d130305 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20213, d130305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20213, d130305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro10827 (p : Pattern) (selected : d20230 p = 1) : d130311 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20214 q = 1) : d130306 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20214, d130306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20214, d130306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10826 q selected
  have h2 (q : Pattern) (selected : d20225 q = 1) : d20225 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d20226 q = 1) : d130307 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20226, d130307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20226, d130307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20227 q = 1) : d130308 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d20227, d130308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20227, d130308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20228 q = 1) : d130309 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d20228, d130309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20228, d130309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20229 q = 1) : d130310 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d20229, d130310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20229, d130310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20230 q = 1) : d130311 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d20230, d130311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20230, d130311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro10828 (p : Pattern) (selected : d20236 p = 1) : d130317 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20231 q = 1) : d130312 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d20231, d130312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20231, d130312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10827 q selected
  have h2 (q : Pattern) (selected : d20232 q = 1) : d130313 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d20232, d130313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20232, d130313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20233 q = 1) : d130314 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d20233, d130314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20233, d130314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20234 q = 1) : d130315 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d20234, d130315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20234, d130315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20235 q = 1) : d130316 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d20235, d130316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20235, d130316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20236 q = 1) : d130317 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d20236, d130317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20236, d130317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro10829 (p : Pattern) (selected : d20285 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10501 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6875 q selected
    | true =>
      simp only [d10501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6877 q selected
  have h2 (q : Pattern) (selected : d20276 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20277 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10528 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6877 q selected
    | true =>
      simp only [d10528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6880 q selected
  have h5 (q : Pattern) (selected : d20278 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20279 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d20280 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10537 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6877 q selected
    | true =>
      simp only [d10537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6881 q selected
  have h9 (q : Pattern) (selected : d20281 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d20282 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d20283 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d20283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d20284 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d10502 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d10503 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d10529 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d10530 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d10531 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d10531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d10538 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d10539 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d10540 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d10540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d10541 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d10541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d20285 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d20285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  exact h22 p selected
theorem eqIntro10830 (p : Pattern) (selected : d20289 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10537 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6877 q selected
    | true =>
      simp only [d10537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6881 q selected
  have h2 (q : Pattern) (selected : d20281 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20282 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20283 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20288 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10538 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10539 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10540 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10545 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d20289 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro10831 (p : Pattern) (selected : d20295 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20286 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10829 q selected
    | true =>
      simp only [d20286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20287 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20290 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10830 q selected
    | true =>
      simp only [d20290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20291 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20292 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20293 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20294 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d20295 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro10832 (p : Pattern) (selected : d20299 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20290 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10830 q selected
    | true =>
      simp only [d20290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20291 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20296 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20297 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20298 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20299 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10833 (p : Pattern) (selected : d20318 p = 1) : d130326 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20275 q = 1) : d20275 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d20300 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10831 q selected
    | true =>
      simp only [d20300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10832 q selected
  have h3 (q : Pattern) (selected : d20301 q = 1) : d130322 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20301, d130322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20301, d130322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20314 q = 1) : d20314 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d20315 q = 1) : d130323 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20315, d130323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20315, d130323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20316 q = 1) : d130324 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20316, d130324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20316, d130324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d20317 q = 1) : d130325 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20317, d130325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20317, d130325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d20318 q = 1) : d130326 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20318, d130326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20318, d130326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro10834 (p : Pattern) (selected : d20335 p = 1) : d130332 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20319 q = 1) : d130327 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20319, d130327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20319, d130327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10833 q selected
  have h2 (q : Pattern) (selected : d20330 q = 1) : d20330 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d20331 q = 1) : d130328 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20331, d130328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20331, d130328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20332 q = 1) : d130329 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d20332, d130329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20332, d130329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20333 q = 1) : d130330 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d20333, d130330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20333, d130330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20334 q = 1) : d130331 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d20334, d130331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20334, d130331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20335 q = 1) : d130332 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d20335, d130332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20335, d130332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro10835 (p : Pattern) (selected : d20341 p = 1) : d130338 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20336 q = 1) : d130333 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d20336, d130333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20336, d130333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10834 q selected
  have h2 (q : Pattern) (selected : d20337 q = 1) : d130334 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d20337, d130334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20337, d130334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20338 q = 1) : d130335 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d20338, d130335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20338, d130335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20339 q = 1) : d130336 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d20339, d130336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20339, d130336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20340 q = 1) : d130337 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d20340, d130337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20340, d130337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20341 q = 1) : d130338 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d20341, d130338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20341, d130338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro10836 (p : Pattern) (selected : d20347 p = 1) : d130344 p = 1 := by
  have h0 (q : Pattern) (selected : d19940 q = 1) : d130261 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d19940, d130261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10800 q selected
    | true =>
      simp only [d19940, d130261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10807 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d20030 q = 1) : d130279 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d20030, d130279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20030, d130279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10814 q selected
  have h3 (q : Pattern) (selected : d20031 q = 1) : d130280 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d20031, d130280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20031, d130280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20133 q = 1) : d130298 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d20133, d130298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20133, d130298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10821 q selected
  have h5 (q : Pattern) (selected : d20134 q = 1) : d130299 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d20134, d130299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20134, d130299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20135 q = 1) : d130300 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d20135, d130300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20135, d130300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d20237 q = 1) : d130318 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d20237, d130318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20237, d130318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10828 q selected
  have h8 (q : Pattern) (selected : d20238 q = 1) : d130319 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d20238, d130319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20238, d130319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d20239 q = 1) : d130320 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d20239, d130320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20239, d130320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d20240 q = 1) : d130321 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d20240, d130321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20240, d130321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d20342 q = 1) : d130339 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d20342, d130339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20342, d130339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10835 q selected
  have h12 (q : Pattern) (selected : d20343 q = 1) : d130340 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d20343, d130340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20343, d130340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d20344 q = 1) : d130341 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d20344, d130341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20344, d130341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d20345 q = 1) : d130342 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d20345, d130342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20345, d130342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d20346 q = 1) : d130343 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d20346, d130343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d20346, d130343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d20347 q = 1) : d130344 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d20347, d130344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d20347, d130344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro10837 (p : Pattern) (selected : d20353 p = 1) : d130350 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20348 q = 1) : d130345 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d20348, d130345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10836 q selected
    | true =>
      simp only [d20348, d130345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20349 q = 1) : d130346 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d20349, d130346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20349, d130346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d20350 q = 1) : d130347 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d20350, d130347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20350, d130347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20351 q = 1) : d130348 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d20351, d130348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20351, d130348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20352 q = 1) : d130349 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d20352, d130349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20352, d130349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20353 q = 1) : d130350 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d20353, d130350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20353, d130350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10838 (p : Pattern) (selected : d20359 p = 1) : d130356 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20354 q = 1) : d130351 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d20354, d130351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10837 q selected
    | true =>
      simp only [d20354, d130351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20355 q = 1) : d130352 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d20355, d130352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20355, d130352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d20356 q = 1) : d130353 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d20356, d130353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20356, d130353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20357 q = 1) : d130354 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d20357, d130354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20357, d130354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20358 q = 1) : d130355 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d20358, d130355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20358, d130355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20359 q = 1) : d130356 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d20359, d130356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20359, d130356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10839 (p : Pattern) (selected : d20365 p = 1) : d130362 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20360 q = 1) : d130357 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d20360, d130357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10838 q selected
    | true =>
      simp only [d20360, d130357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20361 q = 1) : d130358 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d20361, d130358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20361, d130358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d20362 q = 1) : d130359 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d20362, d130359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20362, d130359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20363 q = 1) : d130360 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d20363, d130360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20363, d130360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20364 q = 1) : d130361 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d20364, d130361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20364, d130361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20365 q = 1) : d130362 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d20365, d130362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20365, d130362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10840 (p : Pattern) (selected : d20371 p = 1) : d130368 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20366 q = 1) : d130363 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d20366, d130363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10839 q selected
    | true =>
      simp only [d20366, d130363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20367 q = 1) : d130364 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d20367, d130364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20367, d130364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d20368 q = 1) : d130365 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d20368, d130365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20368, d130365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20369 q = 1) : d130366 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d20369, d130366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20369, d130366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20370 q = 1) : d130367 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d20370, d130367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20370, d130367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20371 q = 1) : d130368 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d20371, d130368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20371, d130368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10841 (p : Pattern) (selected : d20377 p = 1) : d130374 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20372 q = 1) : d130369 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d20372, d130369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10840 q selected
    | true =>
      simp only [d20372, d130369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20373 q = 1) : d130370 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d20373, d130370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20373, d130370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d20374 q = 1) : d130371 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d20374, d130371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20374, d130371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20375 q = 1) : d130372 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d20375, d130372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20375, d130372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20376 q = 1) : d130373 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d20376, d130373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20376, d130373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20377 q = 1) : d130374 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d20377, d130374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20377, d130374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10842 (p : Pattern) (selected : d20383 p = 1) : d130380 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20378 q = 1) : d130375 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d20378, d130375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10841 q selected
    | true =>
      simp only [d20378, d130375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20379 q = 1) : d130376 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d20379, d130376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20379, d130376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d20380 q = 1) : d130377 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d20380, d130377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20380, d130377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20381 q = 1) : d130378 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d20381, d130378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20381, d130378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20382 q = 1) : d130379 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d20382, d130379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20382, d130379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20383 q = 1) : d130380 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d20383, d130380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20383, d130380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10843 (p : Pattern) (selected : d20389 p = 1) : d130386 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20384 q = 1) : d130381 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d20384, d130381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10842 q selected
    | true =>
      simp only [d20384, d130381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20385 q = 1) : d130382 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d20385, d130382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20385, d130382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d20386 q = 1) : d130383 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d20386, d130383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20386, d130383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20387 q = 1) : d130384 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d20387, d130384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20387, d130384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20388 q = 1) : d130385 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d20388, d130385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20388, d130385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20389 q = 1) : d130386 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d20389, d130386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20389, d130386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10844 (p : Pattern) (selected : d20390 p = 0) : d130483 p = 1 := by
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
  have h4 (q : Pattern) (selected : d75 q = 0) : d51927 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d76 q = 0) : d51928 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d76, d51928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d76, d51928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9297 q = 0) : d100948 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6594 q selected
    | true =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9298 q = 0) : d100949 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9298, d100949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9298, d100949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9299 q = 0) : d100950 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9299, d100950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9299, d100950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d9300 q = 0) : d100951 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9300, d100951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9300, d100951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d9301 q = 0) : d100952 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9301, d100952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d9301, d100952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d20390 q = 0) : d130483 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20390, d130483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20390, d130483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro10845 (p : Pattern) (selected : d20396 p = 0) : d130489 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20391 q = 0) : d130484 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20391, d130484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10844 q selected
    | true =>
      simp only [d20391, d130484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20392 q = 0) : d130485 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20392, d130485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20392, d130485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20393 q = 0) : d130486 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20393, d130486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20393, d130486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20394 q = 0) : d130487 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20394, d130487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20394, d130487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20395 q = 0) : d130488 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20395, d130488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20395, d130488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20396 q = 0) : d130489 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20396, d130489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20396, d130489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10846 (p : Pattern) (selected : d20402 p = 0) : d130495 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20397 q = 0) : d130490 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20397, d130490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10845 q selected
    | true =>
      simp only [d20397, d130490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20398 q = 0) : d130491 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20398, d130491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20398, d130491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d20399 q = 0) : d130492 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20399, d130492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20399, d130492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20400 q = 0) : d130493 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20400, d130493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20400, d130493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20401 q = 0) : d130494 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20401, d130494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20401, d130494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20402 q = 0) : d130495 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20402, d130495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20402, d130495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro10847 (p : Pattern) (selected : d20408 p = 0) : d130501 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20403 q = 0) : d130496 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20403, d130496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20403, d130496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10846 q selected
  have h2 (q : Pattern) (selected : d20404 q = 0) : d130497 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20404, d130497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20404, d130497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d20405 q = 0) : d130498 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d20405, d130498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20405, d130498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20406 q = 0) : d130499 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d20406, d130499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20406, d130499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20407 q = 0) : d130500 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d20407, d130500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20407, d130500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20408 q = 0) : d130501 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d20408, d130501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20408, d130501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro10848 (p : Pattern) (selected : d20413 p = 0) : d130506 p = 1 := by
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
  have h4 (q : Pattern) (selected : d72 q = 0) : d51924 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro195 q selected
    | true =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d73 q = 0) : d51925 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d74 q = 0) : d51926 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d235 q = 0) : d52053 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d52053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d235, d52053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d75 q = 0) : d51927 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d236 q = 0) : d52054 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d236, d52054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d236, d52054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d9330 q = 0) : d100981 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6599 q selected
    | true =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6594 q selected
  have h11 (q : Pattern) (selected : d9331 q = 0) : d100982 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d9332 q = 0) : d100983 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d9297 q = 0) : d100948 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6594 q selected
    | true =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d9298 q = 0) : d100949 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9298, d100949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d9298, d100949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d9299 q = 0) : d100950 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9299, d100950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9299, d100950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d9333 q = 0) : d100984 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9333, d100984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d9333, d100984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d9300 q = 0) : d100951 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9300, d100951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d9300, d100951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d9334 q = 0) : d100985 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9334, d100985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d9334, d100985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d20413 q = 0) : d130506 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20413, d130506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d20413, d130506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro10849 (p : Pattern) (selected : d20419 p = 0) : d130512 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20414 q = 0) : d130507 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20414, d130507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10848 q selected
    | true =>
      simp only [d20414, d130507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20415 q = 0) : d130508 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20415, d130508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20415, d130508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20391 q = 0) : d130484 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20391, d130484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10844 q selected
    | true =>
      simp only [d20391, d130484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20392 q = 0) : d130485 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20392, d130485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20392, d130485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20416 q = 0) : d130509 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20416, d130509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20416, d130509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20417 q = 0) : d130510 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20417, d130510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20417, d130510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20418 q = 0) : d130511 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20418, d130511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20418, d130511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d20419 q = 0) : d130512 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20419, d130512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20419, d130512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro10850 (p : Pattern) (selected : d20421 p = 0) : d130483 p = 1 := by
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
  have h4 (q : Pattern) (selected : d254 q = 0) : d51927 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d254, d51927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254, d51927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255 q = 0) : d51928 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d255, d51928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255, d51928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9348 q = 0) : d100948 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9348, d100948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6602 q selected
    | true =>
      simp only [d9348, d100948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9349 q = 0) : d100949 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9349, d100949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9349, d100949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9350 q = 0) : d100950 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9350, d100950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9350, d100950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d9351 q = 0) : d100951 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9351, d100951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9351, d100951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d9352 q = 0) : d100952 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9352, d100952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d9352, d100952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d20421 q = 0) : d130483 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20421, d130483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20421, d130483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro10851 (p : Pattern) (selected : d20427 p = 0) : d130489 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20422 q = 0) : d130484 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20422, d130484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10850 q selected
    | true =>
      simp only [d20422, d130484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20423 q = 0) : d130485 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20423, d130485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20423, d130485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20424 q = 0) : d130486 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20424, d130486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20424, d130486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20425 q = 0) : d130487 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20425, d130487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20425, d130487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20426 q = 0) : d130488 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20426, d130488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20426, d130488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20427 q = 0) : d130489 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20427, d130489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20427, d130489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10852 (p : Pattern) (selected : d20433 p = 0) : d130518 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20420 q = 0) : d130513 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20420, d130513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10849 q selected
    | true =>
      simp only [d20420, d130513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10845 q selected
  have h2 (q : Pattern) (selected : d20428 q = 0) : d130490 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20428, d130490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10851 q selected
    | true =>
      simp only [d20428, d130490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d20429 q = 0) : d130514 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20429, d130514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20429, d130514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20397 q = 0) : d130490 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20397, d130490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10845 q selected
    | true =>
      simp only [d20397, d130490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20398 q = 0) : d130491 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20398, d130491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20398, d130491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20430 q = 0) : d130515 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20430, d130515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20430, d130515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d20431 q = 0) : d130516 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20431, d130516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20431, d130516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d20432 q = 0) : d130517 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20432, d130517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20432, d130517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d20433 q = 0) : d130518 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20433, d130518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20433, d130518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro10853 (p : Pattern) (selected : d20439 p = 0) : d130524 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20434 q = 0) : d130519 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20434, d130519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20434, d130519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10852 q selected
  have h2 (q : Pattern) (selected : d20435 q = 0) : d130520 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20435, d130520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20435, d130520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d20436 q = 0) : d130521 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d20436, d130521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20436, d130521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20437 q = 0) : d130522 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d20437, d130522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20437, d130522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20438 q = 0) : d130523 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d20438, d130523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20438, d130523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20439 q = 0) : d130524 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d20439, d130524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20439, d130524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro10854 (p : Pattern) (selected : d20445 p = 0) : d130530 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d16005 q = 0) : d126913 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d126913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9870 q selected
    | true =>
      simp only [d16005, d126913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro222 q selected
  have h2 (q : Pattern) (selected : d16006 q = 0) : d126914 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d126914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16006, d126914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d16007 q = 0) : d126915 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d126915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16007, d126915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232 q = 0) : d52050 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro222 q selected
    | true =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro195 q selected
  have h5 (q : Pattern) (selected : d233 q = 0) : d52051 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d234 q = 0) : d52052 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d16008 q = 0) : d126916 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d126916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d16008, d126916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d72 q = 0) : d51924 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro195 q selected
    | true =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d73 q = 0) : d51925 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d74 q = 0) : d51926 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d235 q = 0) : d52053 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d52053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d235, d52053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d16009 q = 0) : d126917 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16009, d126917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d16009, d126917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d9389 q = 0) : d101022 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6608 q selected
    | true =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6599 q selected
  have h14 (q : Pattern) (selected : d9390 q = 0) : d101023 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9390, d101023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d9390, d101023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d9391 q = 0) : d101024 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9391, d101024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9391, d101024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d9330 q = 0) : d100981 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6599 q selected
    | true =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6594 q selected
  have h17 (q : Pattern) (selected : d9331 q = 0) : d100982 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d9332 q = 0) : d100983 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d9392 q = 0) : d101025 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9392, d101025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d9392, d101025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d9297 q = 0) : d100948 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6594 q selected
    | true =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d9298 q = 0) : d100949 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9298, d100949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d9298, d100949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d9299 q = 0) : d100950 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9299, d100950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9299, d100950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d9333 q = 0) : d100984 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9333, d100984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d9333, d100984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  have h24 (q : Pattern) (selected : d9393 q = 0) : d101026 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9393, d101026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d9393, d101026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d20445 q = 0) : d130530 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20445, d130530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d20445, d130530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  exact h25 p selected
theorem eqIntro10855 (p : Pattern) (selected : d20451 p = 0) : d130536 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20446 q = 0) : d130531 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20446, d130531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10854 q selected
    | true =>
      simp only [d20446, d130531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20447 q = 0) : d130532 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20447, d130532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20447, d130532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20414 q = 0) : d130507 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20414, d130507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10848 q selected
    | true =>
      simp only [d20414, d130507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20415 q = 0) : d130508 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20415, d130508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20415, d130508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20448 q = 0) : d130533 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20448, d130533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20448, d130533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20449 q = 0) : d130534 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20449, d130534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20449, d130534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20450 q = 0) : d130535 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20450, d130535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20450, d130535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d20451 q = 0) : d130536 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20451, d130536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20451, d130536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro10856 (p : Pattern) (selected : d20453 p = 0) : d130506 p = 1 := by
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
  have h4 (q : Pattern) (selected : d251 q = 0) : d51924 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d251, d51924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro225 q selected
    | true =>
      simp only [d251, d51924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d252 q = 0) : d51925 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d252, d51925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d252, d51925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d253 q = 0) : d51926 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d253, d51926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253, d51926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d440 q = 0) : d52053 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d440, d52053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d440, d52053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d254 q = 0) : d51927 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d254, d51927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254, d51927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d441 q = 0) : d52054 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d441, d52054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d441, d52054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d9407 q = 0) : d100981 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9407, d100981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6611 q selected
    | true =>
      simp only [d9407, d100981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6602 q selected
  have h11 (q : Pattern) (selected : d9408 q = 0) : d100982 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9408, d100982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d9408, d100982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d9409 q = 0) : d100983 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9409, d100983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9409, d100983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d9348 q = 0) : d100948 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9348, d100948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6602 q selected
    | true =>
      simp only [d9348, d100948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d9349 q = 0) : d100949 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9349, d100949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d9349, d100949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d9350 q = 0) : d100950 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9350, d100950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9350, d100950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d9410 q = 0) : d100984 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9410, d100984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d9410, d100984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d9351 q = 0) : d100951 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9351, d100951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d9351, d100951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d9411 q = 0) : d100985 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9411, d100985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d9411, d100985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d20453 q = 0) : d130506 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20453, d130506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d20453, d130506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro10857 (p : Pattern) (selected : d20459 p = 0) : d130512 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20454 q = 0) : d130507 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20454, d130507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10856 q selected
    | true =>
      simp only [d20454, d130507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20455 q = 0) : d130508 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20455, d130508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20455, d130508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20422 q = 0) : d130484 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20422, d130484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10850 q selected
    | true =>
      simp only [d20422, d130484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20423 q = 0) : d130485 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20423, d130485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20423, d130485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20456 q = 0) : d130509 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20456, d130509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20456, d130509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20457 q = 0) : d130510 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20457, d130510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20457, d130510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20458 q = 0) : d130511 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20458, d130511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20458, d130511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d20459 q = 0) : d130512 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20459, d130512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20459, d130512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro10858 (p : Pattern) (selected : d20465 p = 0) : d130542 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20414 q = 0) : d130507 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20414, d130507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10848 q selected
    | true =>
      simp only [d20414, d130507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20415 q = 0) : d130508 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20415, d130508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20415, d130508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20462 q = 0) : d130539 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20462, d130539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20462, d130539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20463 q = 0) : d130540 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20463, d130540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20463, d130540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20464 q = 0) : d130541 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20464, d130541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20464, d130541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20465 q = 0) : d130542 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20465, d130542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20465, d130542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10859 (p : Pattern) (selected : d20471 p = 0) : d130548 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20452 q = 0) : d130537 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20452, d130537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10855 q selected
    | true =>
      simp only [d20452, d130537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10849 q selected
  have h2 (q : Pattern) (selected : d20460 q = 0) : d130513 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20460, d130513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10857 q selected
    | true =>
      simp only [d20460, d130513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10851 q selected
  have h3 (q : Pattern) (selected : d20461 q = 0) : d130538 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20461, d130538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20461, d130538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20466 q = 0) : d130543 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20466, d130543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10858 q selected
    | true =>
      simp only [d20466, d130543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20467 q = 0) : d130544 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20467, d130544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20467, d130544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20468 q = 0) : d130545 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20468, d130545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20468, d130545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d20469 q = 0) : d130546 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20469, d130546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20469, d130546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d20470 q = 0) : d130547 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20470, d130547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20470, d130547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d20471 q = 0) : d130548 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20471, d130548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20471, d130548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro10860 (p : Pattern) (selected : d20477 p = 0) : d130554 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20397 q = 0) : d130490 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20397, d130490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10845 q selected
    | true =>
      simp only [d20397, d130490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20473 q = 0) : d130550 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20473, d130550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20473, d130550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20474 q = 0) : d130551 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20474, d130551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20474, d130551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20475 q = 0) : d130552 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20475, d130552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20475, d130552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20476 q = 0) : d130553 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20476, d130553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20476, d130553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20477 q = 0) : d130554 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20477, d130554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20477, d130554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro10861 (p : Pattern) (selected : d20483 p = 0) : d130560 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20472 q = 0) : d130549 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20472, d130549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20472, d130549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10859 q selected
  have h2 (q : Pattern) (selected : d20478 q = 0) : d130555 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20478, d130555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20478, d130555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10860 q selected
  have h3 (q : Pattern) (selected : d20479 q = 0) : d130556 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20479, d130556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20479, d130556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20480 q = 0) : d130557 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d20480, d130557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20480, d130557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20481 q = 0) : d130558 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d20481, d130558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20481, d130558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20482 q = 0) : d130559 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d20482, d130559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20482, d130559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20483 q = 0) : d130560 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d20483, d130560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20483, d130560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro10862 (p : Pattern) (selected : d20489 p = 0) : d130566 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20409 q = 0) : d130502 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d20409, d130502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20409, d130502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10847 q selected
  have h2 (q : Pattern) (selected : d20410 q = 0) : d130503 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d20410, d130503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20410, d130503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20411 q = 0) : d130504 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d20411, d130504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20411, d130504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20412 q = 0) : d130505 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d20412, d130505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20412, d130505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20440 q = 0) : d130525 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d20440, d130525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20440, d130525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10853 q selected
  have h6 (q : Pattern) (selected : d20441 q = 0) : d130526 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d20441, d130526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20441, d130526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d20442 q = 0) : d130527 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d20442, d130527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20442, d130527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d20443 q = 0) : d130528 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d20443, d130528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20443, d130528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d20444 q = 0) : d130529 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d20444, d130529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20444, d130529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d20484 q = 0) : d130561 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d20484, d130561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20484, d130561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10861 q selected
  have h11 (q : Pattern) (selected : d20485 q = 0) : d130562 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d20485, d130562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20485, d130562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d20486 q = 0) : d130563 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d20486, d130563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20486, d130563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d20487 q = 0) : d130564 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d20487, d130564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20487, d130564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d20488 q = 0) : d130565 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d20488, d130565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20488, d130565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d20489 q = 0) : d130566 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d20489, d130566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d20489, d130566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro10863 (p : Pattern) (selected : d20490 p = 0) : d130567 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d16163 q = 0) : d127054 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16163, d127054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9900 q selected
    | true =>
      simp only [d16163, d127054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9870 q selected
  have h2 (q : Pattern) (selected : d16164 q = 0) : d127055 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16164, d127055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16164, d127055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d16165 q = 0) : d127056 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16165, d127056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16165, d127056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d16167 q = 0) : d127058 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16167, d127058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9870 q selected
    | true =>
      simp only [d16167, d127058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9901 q selected
  have h5 (q : Pattern) (selected : d16168 q = 0) : d127059 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16168, d127059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16168, d127059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d16169 q = 0) : d127060 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16169, d127060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16169, d127060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d16170 q = 0) : d127061 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16170, d127061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d16170, d127061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d16005 q = 0) : d126913 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d126913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9870 q selected
    | true =>
      simp only [d16005, d126913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro222 q selected
  have h9 (q : Pattern) (selected : d16006 q = 0) : d126914 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d126914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16006, d126914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d16007 q = 0) : d126915 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d126915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16007, d126915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d232 q = 0) : d52050 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro222 q selected
    | true =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro195 q selected
  have h12 (q : Pattern) (selected : d233 q = 0) : d52051 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d234 q = 0) : d52052 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d16008 q = 0) : d126916 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d126916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d16008, d126916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d16171 q = 0) : d127062 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16171, d127062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d16171, d127062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d9475 q = 0) : d101090 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9475, d101090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6621 q selected
    | true =>
      simp only [d9475, d101090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6608 q selected
  have h17 (q : Pattern) (selected : d9476 q = 0) : d101091 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9476, d101091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d9476, d101091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d9477 q = 0) : d101092 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9477, d101092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9477, d101092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d9479 q = 0) : d101094 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9479, d101094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6608 q selected
    | true =>
      simp only [d9479, d101094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6622 q selected
  have h20 (q : Pattern) (selected : d9480 q = 0) : d101095 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9480, d101095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d9480, d101095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d9481 q = 0) : d101096 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9481, d101096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9481, d101096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d9482 q = 0) : d101097 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9482, d101097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d9482, d101097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d9389 q = 0) : d101022 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6608 q selected
    | true =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6599 q selected
  have h24 (q : Pattern) (selected : d9390 q = 0) : d101023 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9390, d101023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d9390, d101023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d9391 q = 0) : d101024 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9391, d101024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9391, d101024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d9330 q = 0) : d100981 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6599 q selected
    | true =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6594 q selected
  have h27 (q : Pattern) (selected : d9331 q = 0) : d100982 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d9332 q = 0) : d100983 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d9392 q = 0) : d101025 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9392, d101025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d9392, d101025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d9483 q = 0) : d101098 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9483, d101098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d9483, d101098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d20490 q = 0) : d130567 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20490, d130567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d20490, d130567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro10864 (p : Pattern) (selected : d20493 p = 0) : d130570 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d16005 q = 0) : d126913 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d126913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9870 q selected
    | true =>
      simp only [d16005, d126913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro222 q selected
  have h2 (q : Pattern) (selected : d16006 q = 0) : d126914 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d126914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16006, d126914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d16007 q = 0) : d126915 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d126915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16007, d126915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d232 q = 0) : d52050 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro222 q selected
    | true =>
      simp only [d232, d52050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro195 q selected
  have h5 (q : Pattern) (selected : d233 q = 0) : d52051 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d233, d52051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d234 q = 0) : d52052 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d234, d52052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d16008 q = 0) : d126916 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d126916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d16008, d126916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d673 q = 0) : d52377 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d52377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d673, d52377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d16175 q = 0) : d127066 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16175, d127066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d16175, d127066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d9389 q = 0) : d101022 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6608 q selected
    | true =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6599 q selected
  have h11 (q : Pattern) (selected : d9390 q = 0) : d101023 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9390, d101023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d9390, d101023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d9391 q = 0) : d101024 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9391, d101024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9391, d101024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d9330 q = 0) : d100981 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6599 q selected
    | true =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6594 q selected
  have h14 (q : Pattern) (selected : d9331 q = 0) : d100982 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d9332 q = 0) : d100983 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d9392 q = 0) : d101025 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9392, d101025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d9392, d101025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d9487 q = 0) : d101102 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9487, d101102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d9487, d101102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d9488 q = 0) : d101103 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9488, d101103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d9488, d101103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d20493 q = 0) : d130570 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20493, d130570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d20493, d130570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro10865 (p : Pattern) (selected : d20499 p = 0) : d130576 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20491 q = 0) : d130568 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20491, d130568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10863 q selected
    | true =>
      simp only [d20491, d130568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20492 q = 0) : d130569 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20492, d130569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20492, d130569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20494 q = 0) : d130571 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20494, d130571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10864 q selected
    | true =>
      simp only [d20494, d130571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20495 q = 0) : d130572 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20495, d130572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20495, d130572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20496 q = 0) : d130573 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20496, d130573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20496, d130573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20497 q = 0) : d130574 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20497, d130574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20497, d130574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20498 q = 0) : d130575 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20498, d130575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20498, d130575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d20499 q = 0) : d130576 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20499, d130576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20499, d130576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro10866 (p : Pattern) (selected : d20500 p = 0) : d130577 p = 1 := by
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
  have h4 (q : Pattern) (selected : d673 q = 0) : d52377 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d52377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d673, d52377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d682 q = 0) : d52386 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d682, d52386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d682, d52386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9330 q = 0) : d100981 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6599 q selected
    | true =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6594 q selected
  have h7 (q : Pattern) (selected : d9331 q = 0) : d100982 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9332 q = 0) : d100983 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d9487 q = 0) : d101102 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9487, d101102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9487, d101102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d9496 q = 0) : d101111 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9496, d101111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d9496, d101111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d20500 q = 0) : d130577 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20500, d130577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20500, d130577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro10867 (p : Pattern) (selected : d20506 p = 0) : d130583 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20494 q = 0) : d130571 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20494, d130571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10864 q selected
    | true =>
      simp only [d20494, d130571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20495 q = 0) : d130572 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20495, d130572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20495, d130572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20501 q = 0) : d130578 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20501, d130578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10866 q selected
    | true =>
      simp only [d20501, d130578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20502 q = 0) : d130579 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20502, d130579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20502, d130579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20503 q = 0) : d130580 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20503, d130580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20503, d130580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20504 q = 0) : d130581 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20504, d130581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20504, d130581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20505 q = 0) : d130582 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20505, d130582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20505, d130582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d20506 q = 0) : d130583 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20506, d130583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20506, d130583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro10868 (p : Pattern) (selected : d20508 p = 0) : d130570 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d16190 q = 0) : d126913 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16190, d126913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9906 q selected
    | true =>
      simp only [d16190, d126913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro256 q selected
  have h2 (q : Pattern) (selected : d16191 q = 0) : d126914 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16191, d126914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16191, d126914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d16192 q = 0) : d126915 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16192, d126915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16192, d126915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d437 q = 0) : d52050 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d437, d52050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro256 q selected
    | true =>
      simp only [d437, d52050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro225 q selected
  have h5 (q : Pattern) (selected : d438 q = 0) : d52051 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d438, d52051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d438, d52051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d439 q = 0) : d52052 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d439, d52052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d439, d52052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d16193 q = 0) : d126916 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16193, d126916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d16193, d126916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d701 q = 0) : d52377 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d701, d52377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d701, d52377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d16194 q = 0) : d127066 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16194, d127066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d16194, d127066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d9519 q = 0) : d101022 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9519, d101022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6629 q selected
    | true =>
      simp only [d9519, d101022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6611 q selected
  have h11 (q : Pattern) (selected : d9520 q = 0) : d101023 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9520, d101023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d9520, d101023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d9521 q = 0) : d101024 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9521, d101024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9521, d101024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d9407 q = 0) : d100981 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9407, d100981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6611 q selected
    | true =>
      simp only [d9407, d100981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6602 q selected
  have h14 (q : Pattern) (selected : d9408 q = 0) : d100982 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9408, d100982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d9408, d100982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d9409 q = 0) : d100983 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9409, d100983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9409, d100983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d9522 q = 0) : d101025 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9522, d101025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d9522, d101025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d9523 q = 0) : d101102 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9523, d101102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d9523, d101102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d9524 q = 0) : d101103 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9524, d101103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d9524, d101103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d20508 q = 0) : d130570 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20508, d130570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d20508, d130570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro10869 (p : Pattern) (selected : d20511 p = 0) : d130577 p = 1 := by
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
  have h4 (q : Pattern) (selected : d701 q = 0) : d52377 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d701, d52377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d701, d52377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d706 q = 0) : d52386 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d706, d52386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d706, d52386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9407 q = 0) : d100981 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9407, d100981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6611 q selected
    | true =>
      simp only [d9407, d100981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6602 q selected
  have h7 (q : Pattern) (selected : d9408 q = 0) : d100982 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9408, d100982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9408, d100982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9409 q = 0) : d100983 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9409, d100983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9409, d100983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d9523 q = 0) : d101102 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9523, d101102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9523, d101102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d9528 q = 0) : d101111 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9528, d101111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d9528, d101111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d20511 q = 0) : d130577 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20511, d130577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20511, d130577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro10870 (p : Pattern) (selected : d20517 p = 0) : d130583 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20509 q = 0) : d130571 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20509, d130571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10868 q selected
    | true =>
      simp only [d20509, d130571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20510 q = 0) : d130572 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20510, d130572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20510, d130572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20512 q = 0) : d130578 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20512, d130578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10869 q selected
    | true =>
      simp only [d20512, d130578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20513 q = 0) : d130579 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20513, d130579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20513, d130579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20514 q = 0) : d130580 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20514, d130580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20514, d130580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20515 q = 0) : d130581 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20515, d130581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20515, d130581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20516 q = 0) : d130582 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20516, d130582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20516, d130582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d20517 q = 0) : d130583 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20517, d130583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20517, d130583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro10871 (p : Pattern) (selected : d20521 p = 0) : d130588 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20512 q = 0) : d130578 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20512, d130578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10869 q selected
    | true =>
      simp only [d20512, d130578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20513 q = 0) : d130579 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20513, d130579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20513, d130579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20518 q = 0) : d130585 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20518, d130585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20518, d130585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20519 q = 0) : d130586 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20519, d130586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20519, d130586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20520 q = 0) : d130587 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20520, d130587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20520, d130587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20521 q = 0) : d130588 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20521, d130588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20521, d130588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10872 (p : Pattern) (selected : d20527 p = 0) : d130594 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20494 q = 0) : d130571 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20494, d130571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10864 q selected
    | true =>
      simp only [d20494, d130571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20495 q = 0) : d130572 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20495, d130572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20495, d130572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20524 q = 0) : d130591 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20524, d130591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20524, d130591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20525 q = 0) : d130592 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20525, d130592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20525, d130592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20526 q = 0) : d130593 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20526, d130593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20526, d130593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20527 q = 0) : d130594 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20527, d130594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20527, d130594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10873 (p : Pattern) (selected : d20533 p = 0) : d130600 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20507 q = 0) : d130584 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20507, d130584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10865 q selected
    | true =>
      simp only [d20507, d130584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10867 q selected
  have h2 (q : Pattern) (selected : d20522 q = 0) : d130589 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20522, d130589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10870 q selected
    | true =>
      simp only [d20522, d130589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10871 q selected
  have h3 (q : Pattern) (selected : d20523 q = 0) : d130590 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20523, d130590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20523, d130590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20528 q = 0) : d130595 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20528, d130595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10872 q selected
    | true =>
      simp only [d20528, d130595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20529 q = 0) : d130596 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20529, d130596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20529, d130596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20530 q = 0) : d130597 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20530, d130597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20530, d130597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d20531 q = 0) : d130598 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20531, d130598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20531, d130598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d20532 q = 0) : d130599 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20532, d130599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20532, d130599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d20533 q = 0) : d130600 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20533, d130600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20533, d130600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro10874 (p : Pattern) (selected : d20538 p = 0) : d130588 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20501 q = 0) : d130578 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20501, d130578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10866 q selected
    | true =>
      simp only [d20501, d130578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20502 q = 0) : d130579 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20502, d130579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20502, d130579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20535 q = 0) : d130585 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20535, d130585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20535, d130585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20536 q = 0) : d130586 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20536, d130586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20536, d130586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20537 q = 0) : d130587 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20537, d130587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20537, d130587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20538 q = 0) : d130588 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20538, d130588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20538, d130588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10875 (p : Pattern) (selected : d20544 p = 0) : d130607 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20539 q = 0) : d130602 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20539, d130602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10874 q selected
    | true =>
      simp only [d20539, d130602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20540 q = 0) : d130603 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20540, d130603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20540, d130603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20541 q = 0) : d130604 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20541, d130604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20541, d130604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20542 q = 0) : d130605 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20542, d130605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20542, d130605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20543 q = 0) : d130606 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20543, d130606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20543, d130606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20544 q = 0) : d130607 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20544, d130607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20544, d130607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro10876 (p : Pattern) (selected : d20550 p = 0) : d130613 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20534 q = 0) : d130601 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20534, d130601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20534, d130601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10873 q selected
  have h2 (q : Pattern) (selected : d20545 q = 0) : d130608 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20545, d130608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20545, d130608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10875 q selected
  have h3 (q : Pattern) (selected : d20546 q = 0) : d130609 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20546, d130609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20546, d130609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20547 q = 0) : d130610 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d20547, d130610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20547, d130610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20548 q = 0) : d130611 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d20548, d130611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20548, d130611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20549 q = 0) : d130612 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d20549, d130612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20549, d130612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20550 q = 0) : d130613 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d20550, d130613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20550, d130613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro10877 (p : Pattern) (selected : d20556 p = 0) : d130619 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20551 q = 0) : d130614 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d20551, d130614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20551, d130614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10876 q selected
  have h2 (q : Pattern) (selected : d20552 q = 0) : d130615 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d20552, d130615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20552, d130615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20553 q = 0) : d130616 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d20553, d130616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20553, d130616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20554 q = 0) : d130617 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d20554, d130617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20554, d130617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20555 q = 0) : d130618 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d20555, d130618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20555, d130618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20556 q = 0) : d130619 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d20556, d130619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20556, d130619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro10878 (p : Pattern) (selected : d20558 p = 0) : d130621 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d16364 q = 0) : d127221 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16364, d127221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9938 q selected
    | true =>
      simp only [d16364, d127221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9939 q selected
  have h2 (q : Pattern) (selected : d16365 q = 0) : d127222 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16365, d127222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16365, d127222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d16366 q = 0) : d127223 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16366, d127223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16366, d127223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d16368 q = 0) : d127225 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16368, d127225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9939 q selected
    | true =>
      simp only [d16368, d127225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9940 q selected
  have h5 (q : Pattern) (selected : d16369 q = 0) : d127226 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16369, d127226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16369, d127226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d16370 q = 0) : d127227 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16370, d127227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16370, d127227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d16371 q = 0) : d127228 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16371, d127228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d16371, d127228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d16372 q = 0) : d127229 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16372, d127229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9939 q selected
    | true =>
      simp only [d16372, d127229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro365 q selected
  have h9 (q : Pattern) (selected : d16373 q = 0) : d127230 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16373, d127230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16373, d127230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d16374 q = 0) : d127231 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16374, d127231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16374, d127231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d987 q = 0) : d52606 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d52606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro365 q selected
    | true =>
      simp only [d987, d52606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro366 q selected
  have h12 (q : Pattern) (selected : d988 q = 0) : d52607 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d52607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d988, d52607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d989 q = 0) : d52608 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d52608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d989, d52608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d16375 q = 0) : d127232 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16375, d127232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d16375, d127232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d16376 q = 0) : d127233 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16376, d127233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d16376, d127233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d9609 q = 0) : d101189 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9609, d101189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6643 q selected
    | true =>
      simp only [d9609, d101189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6644 q selected
  have h17 (q : Pattern) (selected : d9610 q = 0) : d101190 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9610, d101190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d9610, d101190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d9611 q = 0) : d101191 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9611, d101191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9611, d101191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d9614 q = 0) : d101194 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9614, d101194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6644 q selected
    | true =>
      simp only [d9614, d101194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6645 q selected
  have h20 (q : Pattern) (selected : d9615 q = 0) : d101195 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9615, d101195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d9615, d101195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d9616 q = 0) : d101196 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9616, d101196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9616, d101196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d9617 q = 0) : d101197 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9617, d101197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d9617, d101197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d9620 q = 0) : d101200 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9620, d101200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6644 q selected
    | true =>
      simp only [d9620, d101200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6646 q selected
  have h24 (q : Pattern) (selected : d9621 q = 0) : d101201 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9621, d101201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d9621, d101201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d9622 q = 0) : d101202 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9622, d101202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9622, d101202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d9624 q = 0) : d101204 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6646 q selected
    | true =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6647 q selected
  have h27 (q : Pattern) (selected : d9625 q = 0) : d101205 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9625, d101205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d9625, d101205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d9626 q = 0) : d101206 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9626, d101206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9626, d101206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d9627 q = 0) : d101207 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9627, d101207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d9627, d101207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d9628 q = 0) : d101208 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9628, d101208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d9628, d101208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d20558 q = 0) : d130621 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20558, d130621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d20558, d130621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro10879 (p : Pattern) (selected : d20561 p = 0) : d130624 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d16372 q = 0) : d127229 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16372, d127229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9939 q selected
    | true =>
      simp only [d16372, d127229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro365 q selected
  have h2 (q : Pattern) (selected : d16373 q = 0) : d127230 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16373, d127230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16373, d127230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d16374 q = 0) : d127231 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16374, d127231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16374, d127231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d987 q = 0) : d52606 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d52606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro365 q selected
    | true =>
      simp only [d987, d52606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro366 q selected
  have h5 (q : Pattern) (selected : d988 q = 0) : d52607 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d52607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d988, d52607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d989 q = 0) : d52608 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d52608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d989, d52608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d16375 q = 0) : d127232 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16375, d127232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d16375, d127232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d995 q = 0) : d52614 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d52614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d995, d52614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d16380 q = 0) : d127237 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16380, d127237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d16380, d127237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d9620 q = 0) : d101200 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9620, d101200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6644 q selected
    | true =>
      simp only [d9620, d101200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6646 q selected
  have h11 (q : Pattern) (selected : d9621 q = 0) : d101201 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9621, d101201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d9621, d101201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d9622 q = 0) : d101202 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9622, d101202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9622, d101202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d9624 q = 0) : d101204 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6646 q selected
    | true =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6647 q selected
  have h14 (q : Pattern) (selected : d9625 q = 0) : d101205 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9625, d101205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d9625, d101205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d9626 q = 0) : d101206 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9626, d101206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9626, d101206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d9627 q = 0) : d101207 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9627, d101207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d9627, d101207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d9632 q = 0) : d101212 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9632, d101212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d9632, d101212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d9633 q = 0) : d101213 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9633, d101213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d9633, d101213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d20561 q = 0) : d130624 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20561, d130624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d20561, d130624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro10880 (p : Pattern) (selected : d20567 p = 0) : d130630 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20559 q = 0) : d130622 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20559, d130622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10878 q selected
    | true =>
      simp only [d20559, d130622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20560 q = 0) : d130623 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20560, d130623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20560, d130623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20562 q = 0) : d130625 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20562, d130625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10879 q selected
    | true =>
      simp only [d20562, d130625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20563 q = 0) : d130626 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20563, d130626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20563, d130626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20564 q = 0) : d130627 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20564, d130627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20564, d130627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20565 q = 0) : d130628 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20565, d130628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20565, d130628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20566 q = 0) : d130629 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20566, d130629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20566, d130629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d20567 q = 0) : d130630 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20567, d130630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20567, d130630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro10881 (p : Pattern) (selected : d20568 p = 0) : d130631 p = 1 := by
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
  have h4 (q : Pattern) (selected : d995 q = 0) : d52614 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d52614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d995, d52614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1004 q = 0) : d52623 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1004, d52623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1004, d52623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9624 q = 0) : d101204 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6646 q selected
    | true =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6647 q selected
  have h7 (q : Pattern) (selected : d9625 q = 0) : d101205 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9625, d101205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9625, d101205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9626 q = 0) : d101206 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9626, d101206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9626, d101206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d9632 q = 0) : d101212 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9632, d101212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9632, d101212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d9641 q = 0) : d101221 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9641, d101221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d9641, d101221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d20568 q = 0) : d130631 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20568, d130631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20568, d130631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro10882 (p : Pattern) (selected : d20574 p = 0) : d130637 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20562 q = 0) : d130625 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20562, d130625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10879 q selected
    | true =>
      simp only [d20562, d130625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20563 q = 0) : d130626 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20563, d130626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20563, d130626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20569 q = 0) : d130632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20569, d130632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10881 q selected
    | true =>
      simp only [d20569, d130632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20570 q = 0) : d130633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20570, d130633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20570, d130633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20571 q = 0) : d130634 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20571, d130634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20571, d130634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20572 q = 0) : d130635 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20572, d130635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20572, d130635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20573 q = 0) : d130636 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20573, d130636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20573, d130636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d20574 q = 0) : d130637 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20574, d130637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20574, d130637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro10883 (p : Pattern) (selected : d20576 p = 0) : d130624 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d16400 q = 0) : d127229 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16400, d127229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9945 q selected
    | true =>
      simp only [d16400, d127229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro373 q selected
  have h2 (q : Pattern) (selected : d16401 q = 0) : d127230 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16401, d127230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16401, d127230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d16402 q = 0) : d127231 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16402, d127231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16402, d127231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1030 q = 0) : d52606 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1030, d52606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro373 q selected
    | true =>
      simp only [d1030, d52606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro374 q selected
  have h5 (q : Pattern) (selected : d1031 q = 0) : d52607 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1031, d52607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1031, d52607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1032 q = 0) : d52608 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1032, d52608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1032, d52608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d16403 q = 0) : d127232 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16403, d127232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d16403, d127232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d1034 q = 0) : d52614 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1034, d52614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1034, d52614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d16404 q = 0) : d127237 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16404, d127237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d16404, d127237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d9684 q = 0) : d101200 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9684, d101200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6656 q selected
    | true =>
      simp only [d9684, d101200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6657 q selected
  have h11 (q : Pattern) (selected : d9685 q = 0) : d101201 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9685, d101201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d9685, d101201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d9686 q = 0) : d101202 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9686, d101202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9686, d101202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d9688 q = 0) : d101204 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9688, d101204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6657 q selected
    | true =>
      simp only [d9688, d101204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6658 q selected
  have h14 (q : Pattern) (selected : d9689 q = 0) : d101205 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9689, d101205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d9689, d101205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d9690 q = 0) : d101206 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9690, d101206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9690, d101206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d9691 q = 0) : d101207 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9691, d101207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d9691, d101207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d9692 q = 0) : d101212 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9692, d101212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d9692, d101212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d9693 q = 0) : d101213 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9693, d101213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d9693, d101213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d20576 q = 0) : d130624 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20576, d130624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d20576, d130624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro10884 (p : Pattern) (selected : d20579 p = 0) : d130631 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1030 q = 0) : d52606 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1030, d52606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro373 q selected
    | true =>
      simp only [d1030, d52606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro374 q selected
  have h2 (q : Pattern) (selected : d1031 q = 0) : d52607 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1031, d52607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1031, d52607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1032 q = 0) : d52608 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1032, d52608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1032, d52608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1034 q = 0) : d52614 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1034, d52614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1034, d52614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1039 q = 0) : d52623 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1039, d52623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1039, d52623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9688 q = 0) : d101204 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9688, d101204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6657 q selected
    | true =>
      simp only [d9688, d101204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6658 q selected
  have h7 (q : Pattern) (selected : d9689 q = 0) : d101205 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9689, d101205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9689, d101205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9690 q = 0) : d101206 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9690, d101206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9690, d101206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d9692 q = 0) : d101212 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9692, d101212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9692, d101212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d9697 q = 0) : d101221 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9697, d101221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d9697, d101221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d20579 q = 0) : d130631 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20579, d130631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20579, d130631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro10885 (p : Pattern) (selected : d20585 p = 0) : d130637 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20577 q = 0) : d130625 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20577, d130625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10883 q selected
    | true =>
      simp only [d20577, d130625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20578 q = 0) : d130626 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20578, d130626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20578, d130626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20580 q = 0) : d130632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20580, d130632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10884 q selected
    | true =>
      simp only [d20580, d130632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20581 q = 0) : d130633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20581, d130633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20581, d130633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20582 q = 0) : d130634 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20582, d130634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20582, d130634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20583 q = 0) : d130635 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20583, d130635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20583, d130635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20584 q = 0) : d130636 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20584, d130636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20584, d130636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d20585 q = 0) : d130637 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20585, d130637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20585, d130637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro10886 (p : Pattern) (selected : d20589 p = 0) : d130642 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20580 q = 0) : d130632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20580, d130632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10884 q selected
    | true =>
      simp only [d20580, d130632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20581 q = 0) : d130633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20581, d130633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20581, d130633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20586 q = 0) : d130639 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20586, d130639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20586, d130639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20587 q = 0) : d130640 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20587, d130640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20587, d130640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20588 q = 0) : d130641 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20588, d130641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20588, d130641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20589 q = 0) : d130642 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20589, d130642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20589, d130642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10887 (p : Pattern) (selected : d20595 p = 0) : d130648 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20562 q = 0) : d130625 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20562, d130625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10879 q selected
    | true =>
      simp only [d20562, d130625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20563 q = 0) : d130626 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20563, d130626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20563, d130626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20592 q = 0) : d130645 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20592, d130645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20592, d130645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20593 q = 0) : d130646 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20593, d130646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20593, d130646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20594 q = 0) : d130647 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20594, d130647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20594, d130647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20595 q = 0) : d130648 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20595, d130648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20595, d130648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10888 (p : Pattern) (selected : d20601 p = 0) : d130654 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20575 q = 0) : d130638 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20575, d130638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10880 q selected
    | true =>
      simp only [d20575, d130638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10882 q selected
  have h2 (q : Pattern) (selected : d20590 q = 0) : d130643 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20590, d130643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10885 q selected
    | true =>
      simp only [d20590, d130643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10886 q selected
  have h3 (q : Pattern) (selected : d20591 q = 0) : d130644 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20591, d130644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20591, d130644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20596 q = 0) : d130649 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20596, d130649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10887 q selected
    | true =>
      simp only [d20596, d130649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20597 q = 0) : d130650 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20597, d130650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20597, d130650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20598 q = 0) : d130651 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20598, d130651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20598, d130651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d20599 q = 0) : d130652 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20599, d130652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20599, d130652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d20600 q = 0) : d130653 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20600, d130653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20600, d130653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d20601 q = 0) : d130654 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20601, d130654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20601, d130654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro10889 (p : Pattern) (selected : d20606 p = 0) : d130642 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20569 q = 0) : d130632 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20569, d130632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10881 q selected
    | true =>
      simp only [d20569, d130632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20570 q = 0) : d130633 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20570, d130633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20570, d130633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20603 q = 0) : d130639 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20603, d130639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20603, d130639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20604 q = 0) : d130640 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20604, d130640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20604, d130640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20605 q = 0) : d130641 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20605, d130641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20605, d130641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20606 q = 0) : d130642 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20606, d130642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20606, d130642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10890 (p : Pattern) (selected : d20612 p = 0) : d130661 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20607 q = 0) : d130656 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20607, d130656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10889 q selected
    | true =>
      simp only [d20607, d130656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20608 q = 0) : d130657 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20608, d130657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20608, d130657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20609 q = 0) : d130658 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20609, d130658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20609, d130658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20610 q = 0) : d130659 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20610, d130659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20610, d130659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20611 q = 0) : d130660 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20611, d130660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20611, d130660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20612 q = 0) : d130661 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20612, d130661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20612, d130661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro10891 (p : Pattern) (selected : d20618 p = 0) : d130667 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20602 q = 0) : d130655 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20602, d130655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20602, d130655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10888 q selected
  have h2 (q : Pattern) (selected : d20613 q = 0) : d130662 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20613, d130662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20613, d130662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10890 q selected
  have h3 (q : Pattern) (selected : d20614 q = 0) : d130663 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20614, d130663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20614, d130663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20615 q = 0) : d130664 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d20615, d130664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20615, d130664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20616 q = 0) : d130665 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d20616, d130665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20616, d130665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20617 q = 0) : d130666 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d20617, d130666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20617, d130666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20618 q = 0) : d130667 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d20618, d130667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20618, d130667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro10892 (p : Pattern) (selected : d20624 p = 0) : d130673 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20619 q = 0) : d130668 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d20619, d130668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20619, d130668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10891 q selected
  have h2 (q : Pattern) (selected : d20620 q = 0) : d130669 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d20620, d130669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20620, d130669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20621 q = 0) : d130670 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d20621, d130670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20621, d130670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20622 q = 0) : d130671 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d20622, d130671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20622, d130671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20623 q = 0) : d130672 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d20623, d130672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20623, d130672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20624 q = 0) : d130673 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d20624, d130673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20624, d130673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro10893 (p : Pattern) (selected : d20627 p = 0) : d130676 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d16663 q = 0) : d127464 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16663, d127464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9995 q selected
    | true =>
      simp only [d16663, d127464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9996 q selected
  have h2 (q : Pattern) (selected : d16664 q = 0) : d127465 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16664, d127465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16664, d127465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d16665 q = 0) : d127466 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16665, d127466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16665, d127466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d16668 q = 0) : d127469 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16668, d127469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9996 q selected
    | true =>
      simp only [d16668, d127469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9997 q selected
  have h5 (q : Pattern) (selected : d16669 q = 0) : d127470 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16669, d127470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16669, d127470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d16670 q = 0) : d127471 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16670, d127471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16670, d127471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d16671 q = 0) : d127472 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16671, d127472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d16671, d127472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d16673 q = 0) : d127474 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d127474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9996 q selected
    | true =>
      simp only [d16673, d127474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9998 q selected
  have h9 (q : Pattern) (selected : d16674 q = 0) : d127475 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d127475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16674, d127475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d16675 q = 0) : d127476 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d127476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16675, d127476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d16676 q = 0) : d127477 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d127477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9998 q selected
    | true =>
      simp only [d16676, d127477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9551 q selected
  have h12 (q : Pattern) (selected : d16677 q = 0) : d127478 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d127478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16677, d127478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d16678 q = 0) : d127479 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d127479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16678, d127479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d16679 q = 0) : d127480 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d127480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d16679, d127480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d16680 q = 0) : d127481 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16680, d127481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d16680, d127481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d9807 q = 0) : d101328 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9807, d101328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6673 q selected
    | true =>
      simp only [d9807, d101328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6676 q selected
  have h17 (q : Pattern) (selected : d9808 q = 0) : d101329 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9808, d101329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d9808, d101329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d9809 q = 0) : d101330 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9809, d101330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9809, d101330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d9822 q = 0) : d101343 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9822, d101343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6676 q selected
    | true =>
      simp only [d9822, d101343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6678 q selected
  have h20 (q : Pattern) (selected : d9823 q = 0) : d101344 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9823, d101344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d9823, d101344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d9824 q = 0) : d101345 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9824, d101345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9824, d101345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d9825 q = 0) : d101346 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9825, d101346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d9825, d101346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d9834 q = 0) : d101355 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6676 q selected
    | true =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6679 q selected
  have h24 (q : Pattern) (selected : d9835 q = 0) : d101356 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d9836 q = 0) : d101357 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d9851 q = 0) : d101372 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6679 q selected
    | true =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6681 q selected
  have h27 (q : Pattern) (selected : d9852 q = 0) : d101373 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d9853 q = 0) : d101374 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d9854 q = 0) : d101375 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d9855 q = 0) : d101376 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9855, d101376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d9855, d101376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d20627 q = 0) : d130676 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20627, d130676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d20627, d130676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro10894 (p : Pattern) (selected : d20630 p = 0) : d130679 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d16673 q = 0) : d127474 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d127474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9996 q selected
    | true =>
      simp only [d16673, d127474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9998 q selected
  have h2 (q : Pattern) (selected : d16674 q = 0) : d127475 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d127475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16674, d127475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d16675 q = 0) : d127476 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d127476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16675, d127476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d16676 q = 0) : d127477 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d127477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9998 q selected
    | true =>
      simp only [d16676, d127477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9551 q selected
  have h5 (q : Pattern) (selected : d16677 q = 0) : d127478 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d127478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16677, d127478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d16678 q = 0) : d127479 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d127479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16678, d127479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d16679 q = 0) : d127480 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d127480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d16679, d127480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d16684 q = 0) : d127485 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16684, d127485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d16684, d127485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d16685 q = 0) : d127486 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16685, d127486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d16685, d127486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d9834 q = 0) : d101355 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6676 q selected
    | true =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6679 q selected
  have h11 (q : Pattern) (selected : d9835 q = 0) : d101356 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d9836 q = 0) : d101357 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d9851 q = 0) : d101372 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6679 q selected
    | true =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6681 q selected
  have h14 (q : Pattern) (selected : d9852 q = 0) : d101373 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d9853 q = 0) : d101374 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d9854 q = 0) : d101375 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d9859 q = 0) : d101380 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9859, d101380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d9859, d101380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d9860 q = 0) : d101381 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9860, d101381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d9860, d101381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d20630 q = 0) : d130679 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20630, d130679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d20630, d130679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro10895 (p : Pattern) (selected : d20636 p = 0) : d130685 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20628 q = 0) : d130677 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20628, d130677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10893 q selected
    | true =>
      simp only [d20628, d130677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20629 q = 0) : d130678 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20629, d130678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20629, d130678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20631 q = 0) : d130680 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20631, d130680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10894 q selected
    | true =>
      simp only [d20631, d130680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20632 q = 0) : d130681 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20632, d130681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20632, d130681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20633 q = 0) : d130682 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20633, d130682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20633, d130682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20634 q = 0) : d130683 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20634, d130683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20634, d130683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20635 q = 0) : d130684 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20635, d130684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20635, d130684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d20636 q = 0) : d130685 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20636, d130685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20636, d130685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro10896 (p : Pattern) (selected : d20637 p = 0) : d130686 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d16693 q = 0) : d127494 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16693, d127494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9998 q selected
    | true =>
      simp only [d16693, d127494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9555 q selected
  have h2 (q : Pattern) (selected : d16694 q = 0) : d127495 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16694, d127495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16694, d127495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d16695 q = 0) : d127496 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16695, d127496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16695, d127496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d16696 q = 0) : d127497 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16696, d127497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d16696, d127497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d16697 q = 0) : d127498 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16697, d127498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d16697, d127498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9870 q = 0) : d101391 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9870, d101391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6679 q selected
    | true =>
      simp only [d9870, d101391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6685 q selected
  have h7 (q : Pattern) (selected : d9871 q = 0) : d101392 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9871, d101392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9871, d101392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9872 q = 0) : d101393 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9872, d101393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9872, d101393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d9873 q = 0) : d101394 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9873, d101394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9873, d101394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d9874 q = 0) : d101395 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9874, d101395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d9874, d101395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d20637 q = 0) : d130686 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20637, d130686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20637, d130686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro10897 (p : Pattern) (selected : d20643 p = 0) : d130692 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20631 q = 0) : d130680 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20631, d130680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10894 q selected
    | true =>
      simp only [d20631, d130680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20632 q = 0) : d130681 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20632, d130681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20632, d130681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20638 q = 0) : d130687 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20638, d130687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10896 q selected
    | true =>
      simp only [d20638, d130687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20639 q = 0) : d130688 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20639, d130688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20639, d130688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20640 q = 0) : d130689 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20640, d130689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20640, d130689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20641 q = 0) : d130690 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20641, d130690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20641, d130690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20642 q = 0) : d130691 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20642, d130691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20642, d130691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d20643 q = 0) : d130692 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20643, d130692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20643, d130692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro10898 (p : Pattern) (selected : d20645 p = 0) : d130694 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d16714 q = 0) : d127474 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16714, d127474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10004 q selected
    | true =>
      simp only [d16714, d127474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10005 q selected
  have h2 (q : Pattern) (selected : d16715 q = 0) : d127475 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16715, d127475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16715, d127475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d16716 q = 0) : d127476 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16716, d127476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16716, d127476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d16717 q = 0) : d127477 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16717, d127477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10005 q selected
    | true =>
      simp only [d16717, d127477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9560 q selected
  have h5 (q : Pattern) (selected : d16718 q = 0) : d127478 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16718, d127478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16718, d127478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d16719 q = 0) : d127479 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16719, d127479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16719, d127479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d16720 q = 0) : d127480 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16720, d127480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d16720, d127480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d16721 q = 0) : d127494 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16721, d127494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10005 q selected
    | true =>
      simp only [d16721, d127494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9561 q selected
  have h9 (q : Pattern) (selected : d16722 q = 0) : d127495 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16722, d127495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16722, d127495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d16723 q = 0) : d127496 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16723, d127496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16723, d127496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d16724 q = 0) : d127497 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16724, d127497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d16724, d127497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d16725 q = 0) : d127507 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16725, d127507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d16725, d127507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d9934 q = 0) : d101355 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9934, d101355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6693 q selected
    | true =>
      simp only [d9934, d101355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6694 q selected
  have h14 (q : Pattern) (selected : d9935 q = 0) : d101356 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9935, d101356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d9935, d101356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d9936 q = 0) : d101357 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9936, d101357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9936, d101357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d9959 q = 0) : d101372 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9959, d101372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6694 q selected
    | true =>
      simp only [d9959, d101372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6697 q selected
  have h17 (q : Pattern) (selected : d9960 q = 0) : d101373 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9960, d101373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d9960, d101373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d9961 q = 0) : d101374 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9961, d101374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9961, d101374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d9962 q = 0) : d101375 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9962, d101375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d9962, d101375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d9965 q = 0) : d101391 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9965, d101391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6694 q selected
    | true =>
      simp only [d9965, d101391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6698 q selected
  have h21 (q : Pattern) (selected : d9966 q = 0) : d101392 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9966, d101392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d9966, d101392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d9967 q = 0) : d101393 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9967, d101393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9967, d101393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d9968 q = 0) : d101394 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9968, d101394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d9968, d101394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d9969 q = 0) : d101404 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9969, d101404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d9969, d101404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d20645 q = 0) : d130694 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20645, d130694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d20645, d130694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  exact h25 p selected
theorem eqIntro10899 (p : Pattern) (selected : d20648 p = 0) : d130686 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d16721 q = 0) : d127494 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16721, d127494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10005 q selected
    | true =>
      simp only [d16721, d127494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9561 q selected
  have h2 (q : Pattern) (selected : d16722 q = 0) : d127495 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16722, d127495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16722, d127495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d16723 q = 0) : d127496 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16723, d127496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16723, d127496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d16724 q = 0) : d127497 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16724, d127497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d16724, d127497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d16729 q = 0) : d127498 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16729, d127498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d16729, d127498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9965 q = 0) : d101391 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9965, d101391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6694 q selected
    | true =>
      simp only [d9965, d101391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6698 q selected
  have h7 (q : Pattern) (selected : d9966 q = 0) : d101392 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9966, d101392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9966, d101392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9967 q = 0) : d101393 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9967, d101393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9967, d101393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d9968 q = 0) : d101394 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9968, d101394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9968, d101394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d9973 q = 0) : d101395 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9973, d101395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d9973, d101395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d20648 q = 0) : d130686 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20648, d130686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20648, d130686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro10900 (p : Pattern) (selected : d20654 p = 0) : d130700 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20646 q = 0) : d130695 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20646, d130695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10898 q selected
    | true =>
      simp only [d20646, d130695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20647 q = 0) : d130696 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20647, d130696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20647, d130696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20649 q = 0) : d130687 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20649, d130687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10899 q selected
    | true =>
      simp only [d20649, d130687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20650 q = 0) : d130688 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20650, d130688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20650, d130688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20651 q = 0) : d130697 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20651, d130697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20651, d130697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20652 q = 0) : d130698 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20652, d130698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20652, d130698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20653 q = 0) : d130699 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20653, d130699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20653, d130699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d20654 q = 0) : d130700 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20654, d130700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20654, d130700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro10901 (p : Pattern) (selected : d20658 p = 0) : d130704 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20649 q = 0) : d130687 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20649, d130687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10899 q selected
    | true =>
      simp only [d20649, d130687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20650 q = 0) : d130688 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20650, d130688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20650, d130688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20655 q = 0) : d130701 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20655, d130701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20655, d130701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20656 q = 0) : d130702 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20656, d130702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20656, d130702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20657 q = 0) : d130703 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20657, d130703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20657, d130703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20658 q = 0) : d130704 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20658, d130704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20658, d130704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10902 (p : Pattern) (selected : d20661 p = 0) : d130707 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d16673 q = 0) : d127474 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16673, d127474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9996 q selected
    | true =>
      simp only [d16673, d127474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9998 q selected
  have h2 (q : Pattern) (selected : d16674 q = 0) : d127475 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16674, d127475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16674, d127475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d16675 q = 0) : d127476 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16675, d127476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16675, d127476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d16676 q = 0) : d127477 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16676, d127477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9998 q selected
    | true =>
      simp only [d16676, d127477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9551 q selected
  have h5 (q : Pattern) (selected : d16677 q = 0) : d127478 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16677, d127478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16677, d127478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d16678 q = 0) : d127479 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16678, d127479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16678, d127479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d16679 q = 0) : d127480 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16679, d127480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d16679, d127480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d16743 q = 0) : d127521 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16743, d127521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9998 q selected
    | true =>
      simp only [d16743, d127521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8325 q selected
  have h9 (q : Pattern) (selected : d16744 q = 0) : d127522 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16744, d127522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16744, d127522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d16745 q = 0) : d127523 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16745, d127523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16745, d127523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d16746 q = 0) : d127524 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16746, d127524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d16746, d127524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d16747 q = 0) : d127525 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16747, d127525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d16747, d127525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d9834 q = 0) : d101355 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6676 q selected
    | true =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6679 q selected
  have h14 (q : Pattern) (selected : d9835 q = 0) : d101356 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d9836 q = 0) : d101357 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d9851 q = 0) : d101372 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6679 q selected
    | true =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6681 q selected
  have h17 (q : Pattern) (selected : d9852 q = 0) : d101373 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d9853 q = 0) : d101374 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d9854 q = 0) : d101375 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d9988 q = 0) : d101419 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9988, d101419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6679 q selected
    | true =>
      simp only [d9988, d101419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6703 q selected
  have h21 (q : Pattern) (selected : d9989 q = 0) : d101420 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9989, d101420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d9989, d101420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d9990 q = 0) : d101421 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9990, d101421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9990, d101421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d9991 q = 0) : d101422 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9991, d101422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d9991, d101422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d9992 q = 0) : d101423 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9992, d101423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d9992, d101423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d20661 q = 0) : d130707 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20661, d130707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d20661, d130707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  exact h25 p selected
theorem eqIntro10903 (p : Pattern) (selected : d20667 p = 0) : d130713 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20662 q = 0) : d130708 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20662, d130708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10902 q selected
    | true =>
      simp only [d20662, d130708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20663 q = 0) : d130709 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20663, d130709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20663, d130709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20664 q = 0) : d130710 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20664, d130710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20664, d130710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20665 q = 0) : d130711 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20665, d130711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20665, d130711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20666 q = 0) : d130712 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20666, d130712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20666, d130712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20667 q = 0) : d130713 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20667, d130713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20667, d130713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10904 (p : Pattern) (selected : d20673 p = 0) : d130719 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20644 q = 0) : d130693 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20644, d130693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10895 q selected
    | true =>
      simp only [d20644, d130693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10897 q selected
  have h2 (q : Pattern) (selected : d20659 q = 0) : d130705 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20659, d130705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10900 q selected
    | true =>
      simp only [d20659, d130705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10901 q selected
  have h3 (q : Pattern) (selected : d20660 q = 0) : d130706 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20660, d130706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20660, d130706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20668 q = 0) : d130714 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20668, d130714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10903 q selected
    | true =>
      simp only [d20668, d130714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20669 q = 0) : d130715 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20669, d130715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20669, d130715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20670 q = 0) : d130716 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20670, d130716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20670, d130716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d20671 q = 0) : d130717 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20671, d130717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20671, d130717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d20672 q = 0) : d130718 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20672, d130718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20672, d130718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d20673 q = 0) : d130719 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20673, d130719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20673, d130719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro10905 (p : Pattern) (selected : d20678 p = 0) : d130704 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20638 q = 0) : d130687 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20638, d130687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10896 q selected
    | true =>
      simp only [d20638, d130687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20639 q = 0) : d130688 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20639, d130688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20639, d130688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20675 q = 0) : d130701 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20675, d130701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20675, d130701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20676 q = 0) : d130702 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20676, d130702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20676, d130702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20677 q = 0) : d130703 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20677, d130703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20677, d130703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20678 q = 0) : d130704 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20678, d130704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20678, d130704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10906 (p : Pattern) (selected : d20684 p = 0) : d130726 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20679 q = 0) : d130721 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20679, d130721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10905 q selected
    | true =>
      simp only [d20679, d130721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20680 q = 0) : d130722 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20680, d130722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20680, d130722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20681 q = 0) : d130723 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20681, d130723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20681, d130723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20682 q = 0) : d130724 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20682, d130724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20682, d130724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20683 q = 0) : d130725 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20683, d130725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20683, d130725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20684 q = 0) : d130726 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20684, d130726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20684, d130726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro10907 (p : Pattern) (selected : d20690 p = 0) : d130732 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20674 q = 0) : d130720 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20674, d130720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20674, d130720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10904 q selected
  have h2 (q : Pattern) (selected : d20685 q = 0) : d130727 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20685, d130727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20685, d130727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10906 q selected
  have h3 (q : Pattern) (selected : d20686 q = 0) : d130728 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20686, d130728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20686, d130728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20687 q = 0) : d130729 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d20687, d130729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20687, d130729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20688 q = 0) : d130730 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d20688, d130730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20688, d130730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20689 q = 0) : d130731 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d20689, d130731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20689, d130731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20690 q = 0) : d130732 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d20690, d130732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20690, d130732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro10908 (p : Pattern) (selected : d20696 p = 0) : d130738 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20691 q = 0) : d130733 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d20691, d130733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20691, d130733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10907 q selected
  have h2 (q : Pattern) (selected : d20692 q = 0) : d130734 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d20692, d130734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20692, d130734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20693 q = 0) : d130735 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d20693, d130735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20693, d130735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20694 q = 0) : d130736 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d20694, d130736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20694, d130736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20695 q = 0) : d130737 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d20695, d130737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20695, d130737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20696 q = 0) : d130738 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d20696, d130738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20696, d130738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro10909 (p : Pattern) (selected : d20700 p = 0) : d130742 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d17018 q = 0) : d127752 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17018, d127752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10060 q selected
    | true =>
      simp only [d17018, d127752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10061 q selected
  have h2 (q : Pattern) (selected : d17019 q = 0) : d127753 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17019, d127753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17019, d127753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17020 q = 0) : d127754 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17020, d127754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17020, d127754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17023 q = 0) : d127757 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17023, d127757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10061 q selected
    | true =>
      simp only [d17023, d127757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10062 q selected
  have h5 (q : Pattern) (selected : d17024 q = 0) : d127758 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17024, d127758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17024, d127758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17025 q = 0) : d127759 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17025, d127759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17025, d127759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d17026 q = 0) : d127760 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17026, d127760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17026, d127760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d17033 q = 0) : d127767 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17033, d127767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10061 q selected
    | true =>
      simp only [d17033, d127767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10063 q selected
  have h9 (q : Pattern) (selected : d17034 q = 0) : d127768 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d127768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17034, d127768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d17035 q = 0) : d127769 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, d127769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17035, d127769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d17036 q = 0) : d127770 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17036, d127770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10063 q selected
    | true =>
      simp only [d17036, d127770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9624 q selected
  have h12 (q : Pattern) (selected : d17037 q = 0) : d127771 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d127771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17037, d127771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d17038 q = 0) : d127772 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, d127772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17038, d127772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d17039 q = 0) : d127773 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, d127773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d17039, d127773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d17040 q = 0) : d127774 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17040, d127774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d17040, d127774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d10092 q = 0) : d101519 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10092, d101519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6715 q selected
    | true =>
      simp only [d10092, d101519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6718 q selected
  have h17 (q : Pattern) (selected : d10093 q = 0) : d101520 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10093, d101520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d10093, d101520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d10094 q = 0) : d101521 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10094, d101521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10094, d101521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d10107 q = 0) : d101534 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10107, d101534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6718 q selected
    | true =>
      simp only [d10107, d101534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6720 q selected
  have h20 (q : Pattern) (selected : d10108 q = 0) : d101535 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10108, d101535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d10108, d101535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d10109 q = 0) : d101536 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10109, d101536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10109, d101536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d10110 q = 0) : d101537 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10110, d101537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d10110, d101537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d10122 q = 0) : d101549 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6718 q selected
    | true =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6722 q selected
  have h24 (q : Pattern) (selected : d10123 q = 0) : d101550 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d10124 q = 0) : d101551 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d10142 q = 0) : d101569 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6722 q selected
    | true =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6724 q selected
  have h27 (q : Pattern) (selected : d10143 q = 0) : d101570 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d10144 q = 0) : d101571 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d10145 q = 0) : d101572 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d10146 q = 0) : d101573 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10146, d101573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d10146, d101573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d20700 q = 0) : d130742 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20700, d130742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d20700, d130742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro10910 (p : Pattern) (selected : d20703 p = 0) : d130745 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d17033 q = 0) : d127767 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17033, d127767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10061 q selected
    | true =>
      simp only [d17033, d127767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10063 q selected
  have h2 (q : Pattern) (selected : d17034 q = 0) : d127768 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d127768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17034, d127768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17035 q = 0) : d127769 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, d127769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17035, d127769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17036 q = 0) : d127770 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17036, d127770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10063 q selected
    | true =>
      simp only [d17036, d127770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9624 q selected
  have h5 (q : Pattern) (selected : d17037 q = 0) : d127771 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d127771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17037, d127771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17038 q = 0) : d127772 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, d127772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17038, d127772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d17039 q = 0) : d127773 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, d127773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17039, d127773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d17044 q = 0) : d127778 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17044, d127778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17044, d127778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d17045 q = 0) : d127779 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17045, d127779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d17045, d127779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10122 q = 0) : d101549 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6718 q selected
    | true =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6722 q selected
  have h11 (q : Pattern) (selected : d10123 q = 0) : d101550 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d10124 q = 0) : d101551 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d10142 q = 0) : d101569 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6722 q selected
    | true =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6724 q selected
  have h14 (q : Pattern) (selected : d10143 q = 0) : d101570 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d10144 q = 0) : d101571 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d10145 q = 0) : d101572 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d10150 q = 0) : d101577 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10150, d101577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d10150, d101577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d10151 q = 0) : d101578 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10151, d101578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d10151, d101578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d20703 q = 0) : d130745 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20703, d130745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d20703, d130745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro10911 (p : Pattern) (selected : d20709 p = 0) : d130751 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20701 q = 0) : d130743 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20701, d130743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10909 q selected
    | true =>
      simp only [d20701, d130743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20702 q = 0) : d130744 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20702, d130744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20702, d130744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20704 q = 0) : d130746 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20704, d130746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10910 q selected
    | true =>
      simp only [d20704, d130746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20705 q = 0) : d130747 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20705, d130747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20705, d130747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20706 q = 0) : d130748 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20706, d130748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20706, d130748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20707 q = 0) : d130749 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20707, d130749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20707, d130749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20708 q = 0) : d130750 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20708, d130750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20708, d130750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d20709 q = 0) : d130751 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20709, d130751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20709, d130751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro10912 (p : Pattern) (selected : d20710 p = 0) : d130752 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d17053 q = 0) : d127787 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17053, d127787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10063 q selected
    | true =>
      simp only [d17053, d127787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9628 q selected
  have h2 (q : Pattern) (selected : d17054 q = 0) : d127788 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17054, d127788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17054, d127788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17055 q = 0) : d127789 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17055, d127789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17055, d127789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17056 q = 0) : d127790 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17056, d127790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17056, d127790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17057 q = 0) : d127791 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17057, d127791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17057, d127791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10164 q = 0) : d101591 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10164, d101591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6722 q selected
    | true =>
      simp only [d10164, d101591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6728 q selected
  have h7 (q : Pattern) (selected : d10165 q = 0) : d101592 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10165, d101592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10165, d101592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10166 q = 0) : d101593 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10166, d101593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10166, d101593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10167 q = 0) : d101594 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10167, d101594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10167, d101594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d10168 q = 0) : d101595 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10168, d101595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10168, d101595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d20710 q = 0) : d130752 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20710, d130752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20710, d130752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro10913 (p : Pattern) (selected : d20716 p = 0) : d130758 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20704 q = 0) : d130746 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20704, d130746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10910 q selected
    | true =>
      simp only [d20704, d130746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20705 q = 0) : d130747 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20705, d130747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20705, d130747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20711 q = 0) : d130753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20711, d130753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10912 q selected
    | true =>
      simp only [d20711, d130753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20712 q = 0) : d130754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20712, d130754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20712, d130754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20713 q = 0) : d130755 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20713, d130755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20713, d130755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20714 q = 0) : d130756 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20714, d130756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20714, d130756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20715 q = 0) : d130757 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20715, d130757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20715, d130757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d20716 q = 0) : d130758 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20716, d130758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20716, d130758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro10914 (p : Pattern) (selected : d20718 p = 0) : d130760 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d17079 q = 0) : d127767 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17079, d127767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10069 q selected
    | true =>
      simp only [d17079, d127767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10070 q selected
  have h2 (q : Pattern) (selected : d17080 q = 0) : d127768 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17080, d127768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17080, d127768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17081 q = 0) : d127769 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17081, d127769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17081, d127769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17082 q = 0) : d127770 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17082, d127770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10070 q selected
    | true =>
      simp only [d17082, d127770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9633 q selected
  have h5 (q : Pattern) (selected : d17083 q = 0) : d127771 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17083, d127771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17083, d127771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17084 q = 0) : d127772 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17084, d127772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17084, d127772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d17085 q = 0) : d127773 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17085, d127773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17085, d127773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d17086 q = 0) : d127787 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17086, d127787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10070 q selected
    | true =>
      simp only [d17086, d127787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9634 q selected
  have h9 (q : Pattern) (selected : d17087 q = 0) : d127788 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17087, d127788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17087, d127788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d17088 q = 0) : d127789 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17088, d127789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17088, d127789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d17089 q = 0) : d127790 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17089, d127790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d17089, d127790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d17090 q = 0) : d127800 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17090, d127800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d17090, d127800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d10234 q = 0) : d101549 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10234, d101549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6736 q selected
    | true =>
      simp only [d10234, d101549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6738 q selected
  have h14 (q : Pattern) (selected : d10235 q = 0) : d101550 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10235, d101550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d10235, d101550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d10236 q = 0) : d101551 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10236, d101551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10236, d101551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d10262 q = 0) : d101569 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10262, d101569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6738 q selected
    | true =>
      simp only [d10262, d101569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6741 q selected
  have h17 (q : Pattern) (selected : d10263 q = 0) : d101570 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10263, d101570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d10263, d101570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d10264 q = 0) : d101571 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10264, d101571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10264, d101571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d10265 q = 0) : d101572 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10265, d101572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d10265, d101572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d10271 q = 0) : d101591 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10271, d101591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6738 q selected
    | true =>
      simp only [d10271, d101591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6742 q selected
  have h21 (q : Pattern) (selected : d10272 q = 0) : d101592 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10272, d101592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d10272, d101592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d10273 q = 0) : d101593 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10273, d101593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10273, d101593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d10274 q = 0) : d101594 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10274, d101594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d10274, d101594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d10275 q = 0) : d101604 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10275, d101604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d10275, d101604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d20718 q = 0) : d130760 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20718, d130760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d20718, d130760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  exact h25 p selected
theorem eqIntro10915 (p : Pattern) (selected : d20721 p = 0) : d130752 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d17086 q = 0) : d127787 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17086, d127787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10070 q selected
    | true =>
      simp only [d17086, d127787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9634 q selected
  have h2 (q : Pattern) (selected : d17087 q = 0) : d127788 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17087, d127788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17087, d127788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17088 q = 0) : d127789 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17088, d127789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17088, d127789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17089 q = 0) : d127790 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17089, d127790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17089, d127790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17094 q = 0) : d127791 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17094, d127791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17094, d127791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10271 q = 0) : d101591 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10271, d101591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6738 q selected
    | true =>
      simp only [d10271, d101591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6742 q selected
  have h7 (q : Pattern) (selected : d10272 q = 0) : d101592 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10272, d101592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10272, d101592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10273 q = 0) : d101593 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10273, d101593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10273, d101593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10274 q = 0) : d101594 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10274, d101594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10274, d101594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d10279 q = 0) : d101595 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10279, d101595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10279, d101595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d20721 q = 0) : d130752 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20721, d130752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20721, d130752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro10916 (p : Pattern) (selected : d20727 p = 0) : d130766 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20719 q = 0) : d130761 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20719, d130761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10914 q selected
    | true =>
      simp only [d20719, d130761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20720 q = 0) : d130762 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20720, d130762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20720, d130762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20722 q = 0) : d130753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20722, d130753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10915 q selected
    | true =>
      simp only [d20722, d130753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20723 q = 0) : d130754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20723, d130754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20723, d130754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20724 q = 0) : d130763 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20724, d130763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20724, d130763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20725 q = 0) : d130764 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20725, d130764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20725, d130764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20726 q = 0) : d130765 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20726, d130765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20726, d130765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d20727 q = 0) : d130766 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20727, d130766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20727, d130766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro10917 (p : Pattern) (selected : d20731 p = 0) : d130770 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20722 q = 0) : d130753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20722, d130753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10915 q selected
    | true =>
      simp only [d20722, d130753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20723 q = 0) : d130754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20723, d130754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20723, d130754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20728 q = 0) : d130767 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20728, d130767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20728, d130767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20729 q = 0) : d130768 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20729, d130768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20729, d130768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20730 q = 0) : d130769 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20730, d130769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20730, d130769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20731 q = 0) : d130770 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20731, d130770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20731, d130770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10918 (p : Pattern) (selected : d20734 p = 0) : d130773 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d17033 q = 0) : d127767 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17033, d127767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10061 q selected
    | true =>
      simp only [d17033, d127767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10063 q selected
  have h2 (q : Pattern) (selected : d17034 q = 0) : d127768 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17034, d127768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17034, d127768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17035 q = 0) : d127769 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17035, d127769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17035, d127769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17036 q = 0) : d127770 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17036, d127770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10063 q selected
    | true =>
      simp only [d17036, d127770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9624 q selected
  have h5 (q : Pattern) (selected : d17037 q = 0) : d127771 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17037, d127771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17037, d127771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17038 q = 0) : d127772 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17038, d127772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17038, d127772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d17039 q = 0) : d127773 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17039, d127773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17039, d127773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d17108 q = 0) : d127814 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17108, d127814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10063 q selected
    | true =>
      simp only [d17108, d127814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8394 q selected
  have h9 (q : Pattern) (selected : d17109 q = 0) : d127815 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17109, d127815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17109, d127815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d17110 q = 0) : d127816 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17110, d127816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17110, d127816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d17111 q = 0) : d127817 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17111, d127817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d17111, d127817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d17112 q = 0) : d127818 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17112, d127818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d17112, d127818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d10122 q = 0) : d101549 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6718 q selected
    | true =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6722 q selected
  have h14 (q : Pattern) (selected : d10123 q = 0) : d101550 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d10124 q = 0) : d101551 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d10142 q = 0) : d101569 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6722 q selected
    | true =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6724 q selected
  have h17 (q : Pattern) (selected : d10143 q = 0) : d101570 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d10144 q = 0) : d101571 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d10145 q = 0) : d101572 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d10294 q = 0) : d101619 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10294, d101619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6722 q selected
    | true =>
      simp only [d10294, d101619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6747 q selected
  have h21 (q : Pattern) (selected : d10295 q = 0) : d101620 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10295, d101620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d10295, d101620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d10296 q = 0) : d101621 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10296, d101621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10296, d101621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d10297 q = 0) : d101622 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10297, d101622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d10297, d101622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d10298 q = 0) : d101623 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10298, d101623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d10298, d101623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d20734 q = 0) : d130773 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20734, d130773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d20734, d130773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  exact h25 p selected
theorem eqIntro10919 (p : Pattern) (selected : d20740 p = 0) : d130779 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20735 q = 0) : d130774 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20735, d130774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10918 q selected
    | true =>
      simp only [d20735, d130774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20736 q = 0) : d130775 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20736, d130775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20736, d130775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20737 q = 0) : d130776 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20737, d130776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20737, d130776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20738 q = 0) : d130777 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20738, d130777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20738, d130777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20739 q = 0) : d130778 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20739, d130778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20739, d130778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20740 q = 0) : d130779 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20740, d130779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20740, d130779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10920 (p : Pattern) (selected : d20746 p = 0) : d130785 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20717 q = 0) : d130759 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20717, d130759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10911 q selected
    | true =>
      simp only [d20717, d130759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10913 q selected
  have h2 (q : Pattern) (selected : d20732 q = 0) : d130771 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20732, d130771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10916 q selected
    | true =>
      simp only [d20732, d130771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10917 q selected
  have h3 (q : Pattern) (selected : d20733 q = 0) : d130772 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20733, d130772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20733, d130772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20741 q = 0) : d130780 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20741, d130780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10919 q selected
    | true =>
      simp only [d20741, d130780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20742 q = 0) : d130781 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20742, d130781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20742, d130781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20743 q = 0) : d130782 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20743, d130782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20743, d130782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d20744 q = 0) : d130783 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20744, d130783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20744, d130783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d20745 q = 0) : d130784 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20745, d130784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20745, d130784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d20746 q = 0) : d130785 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20746, d130785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20746, d130785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro10921 (p : Pattern) (selected : d20751 p = 0) : d130770 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20711 q = 0) : d130753 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20711, d130753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10912 q selected
    | true =>
      simp only [d20711, d130753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20712 q = 0) : d130754 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20712, d130754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20712, d130754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20748 q = 0) : d130767 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20748, d130767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20748, d130767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20749 q = 0) : d130768 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20749, d130768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20749, d130768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20750 q = 0) : d130769 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20750, d130769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20750, d130769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20751 q = 0) : d130770 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20751, d130770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20751, d130770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10922 (p : Pattern) (selected : d20757 p = 0) : d130792 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20752 q = 0) : d130787 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20752, d130787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10921 q selected
    | true =>
      simp only [d20752, d130787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20753 q = 0) : d130788 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20753, d130788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20753, d130788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20754 q = 0) : d130789 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20754, d130789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20754, d130789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20755 q = 0) : d130790 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20755, d130790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20755, d130790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20756 q = 0) : d130791 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20756, d130791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20756, d130791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20757 q = 0) : d130792 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20757, d130792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20757, d130792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro10923 (p : Pattern) (selected : d20763 p = 0) : d130798 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20747 q = 0) : d130786 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20747, d130786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20747, d130786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10920 q selected
  have h2 (q : Pattern) (selected : d20758 q = 0) : d130793 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20758, d130793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20758, d130793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10922 q selected
  have h3 (q : Pattern) (selected : d20759 q = 0) : d130794 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20759, d130794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20759, d130794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20760 q = 0) : d130795 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d20760, d130795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20760, d130795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20761 q = 0) : d130796 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d20761, d130796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20761, d130796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20762 q = 0) : d130797 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d20762, d130797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20762, d130797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20763 q = 0) : d130798 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d20763, d130798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20763, d130798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro10924 (p : Pattern) (selected : d20769 p = 0) : d130804 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20764 q = 0) : d130799 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d20764, d130799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20764, d130799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10923 q selected
  have h2 (q : Pattern) (selected : d20765 q = 0) : d130800 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d20765, d130800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20765, d130800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20766 q = 0) : d130801 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d20766, d130801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20766, d130801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20767 q = 0) : d130802 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d20767, d130802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20767, d130802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20768 q = 0) : d130803 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d20768, d130803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20768, d130803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20769 q = 0) : d130804 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d20769, d130804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20769, d130804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro10925 (p : Pattern) (selected : d20774 p = 0) : d130809 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d17383 q = 0) : d128045 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17383, d128045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10125 q selected
    | true =>
      simp only [d17383, d128045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10126 q selected
  have h2 (q : Pattern) (selected : d17384 q = 0) : d128046 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17384, d128046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17384, d128046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17385 q = 0) : d128047 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17385, d128047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17385, d128047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17387 q = 0) : d128049 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17387, d128049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10126 q selected
    | true =>
      simp only [d17387, d128049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10127 q selected
  have h5 (q : Pattern) (selected : d17388 q = 0) : d128050 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17388, d128050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17388, d128050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17389 q = 0) : d128051 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17389, d128051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17389, d128051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d17390 q = 0) : d128052 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17390, d128052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17390, d128052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d17397 q = 0) : d128059 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d128059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10126 q selected
    | true =>
      simp only [d17397, d128059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10128 q selected
  have h9 (q : Pattern) (selected : d17398 q = 0) : d128060 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d128060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17398, d128060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d17399 q = 0) : d128061 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d128061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17399, d128061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d17400 q = 0) : d128062 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d128062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10128 q selected
    | true =>
      simp only [d17400, d128062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9697 q selected
  have h12 (q : Pattern) (selected : d17401 q = 0) : d128063 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d128063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17401, d128063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d17402 q = 0) : d128064 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d128064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17402, d128064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d17403 q = 0) : d128065 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d128065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d17403, d128065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d17404 q = 0) : d128066 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17404, d128066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d17404, d128066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d10378 q = 0) : d101699 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10378, d101699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6757 q selected
    | true =>
      simp only [d10378, d101699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6760 q selected
  have h17 (q : Pattern) (selected : d10379 q = 0) : d101700 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10379, d101700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d10379, d101700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d10380 q = 0) : d101701 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10380, d101701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10380, d101701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d10383 q = 0) : d101704 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10383, d101704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6760 q selected
    | true =>
      simp only [d10383, d101704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6761 q selected
  have h20 (q : Pattern) (selected : d10384 q = 0) : d101705 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10384, d101705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d10384, d101705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d10385 q = 0) : d101706 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10385, d101706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10385, d101706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d10386 q = 0) : d101707 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10386, d101707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d10386, d101707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d10398 q = 0) : d101719 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6760 q selected
    | true =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6763 q selected
  have h24 (q : Pattern) (selected : d10399 q = 0) : d101720 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d10400 q = 0) : d101721 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d10419 q = 0) : d101740 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6763 q selected
    | true =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6765 q selected
  have h27 (q : Pattern) (selected : d10420 q = 0) : d101741 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d10421 q = 0) : d101742 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d10422 q = 0) : d101743 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d10423 q = 0) : d101744 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10423, d101744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d10423, d101744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d20774 q = 0) : d130809 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20774, d130809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d20774, d130809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro10926 (p : Pattern) (selected : d20777 p = 0) : d130812 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d17397 q = 0) : d128059 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d128059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10126 q selected
    | true =>
      simp only [d17397, d128059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10128 q selected
  have h2 (q : Pattern) (selected : d17398 q = 0) : d128060 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d128060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17398, d128060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17399 q = 0) : d128061 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d128061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17399, d128061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17400 q = 0) : d128062 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d128062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10128 q selected
    | true =>
      simp only [d17400, d128062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9697 q selected
  have h5 (q : Pattern) (selected : d17401 q = 0) : d128063 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d128063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17401, d128063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17402 q = 0) : d128064 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d128064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17402, d128064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d17403 q = 0) : d128065 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d128065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17403, d128065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d17408 q = 0) : d128070 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17408, d128070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d17408, d128070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d17409 q = 0) : d128071 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17409, d128071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d17409, d128071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10398 q = 0) : d101719 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6760 q selected
    | true =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6763 q selected
  have h11 (q : Pattern) (selected : d10399 q = 0) : d101720 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d10400 q = 0) : d101721 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d10419 q = 0) : d101740 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6763 q selected
    | true =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6765 q selected
  have h14 (q : Pattern) (selected : d10420 q = 0) : d101741 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d10421 q = 0) : d101742 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d10422 q = 0) : d101743 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d10427 q = 0) : d101748 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10427, d101748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d10427, d101748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d10428 q = 0) : d101749 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10428, d101749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d10428, d101749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d20777 q = 0) : d130812 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20777, d130812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d20777, d130812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro10927 (p : Pattern) (selected : d20783 p = 0) : d130818 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20775 q = 0) : d130810 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20775, d130810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10925 q selected
    | true =>
      simp only [d20775, d130810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20776 q = 0) : d130811 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20776, d130811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20776, d130811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20778 q = 0) : d130813 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20778, d130813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10926 q selected
    | true =>
      simp only [d20778, d130813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20779 q = 0) : d130814 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20779, d130814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20779, d130814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20780 q = 0) : d130815 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20780, d130815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20780, d130815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20781 q = 0) : d130816 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20781, d130816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20781, d130816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20782 q = 0) : d130817 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20782, d130817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20782, d130817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d20783 q = 0) : d130818 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20783, d130818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20783, d130818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro10928 (p : Pattern) (selected : d20784 p = 0) : d130819 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d17417 q = 0) : d128079 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17417, d128079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10128 q selected
    | true =>
      simp only [d17417, d128079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9701 q selected
  have h2 (q : Pattern) (selected : d17418 q = 0) : d128080 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17418, d128080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17418, d128080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17419 q = 0) : d128081 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17419, d128081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17419, d128081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17420 q = 0) : d128082 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17420, d128082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17420, d128082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17421 q = 0) : d128083 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17421, d128083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17421, d128083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10441 q = 0) : d101762 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10441, d101762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6763 q selected
    | true =>
      simp only [d10441, d101762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6769 q selected
  have h7 (q : Pattern) (selected : d10442 q = 0) : d101763 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10442, d101763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10442, d101763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10443 q = 0) : d101764 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10443, d101764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10443, d101764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10444 q = 0) : d101765 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10444, d101765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10444, d101765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d10445 q = 0) : d101766 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10445, d101766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10445, d101766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d20784 q = 0) : d130819 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20784, d130819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20784, d130819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro10929 (p : Pattern) (selected : d20790 p = 0) : d130825 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20778 q = 0) : d130813 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20778, d130813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10926 q selected
    | true =>
      simp only [d20778, d130813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20779 q = 0) : d130814 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20779, d130814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20779, d130814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20785 q = 0) : d130820 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20785, d130820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10928 q selected
    | true =>
      simp only [d20785, d130820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20786 q = 0) : d130821 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20786, d130821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20786, d130821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20787 q = 0) : d130822 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20787, d130822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20787, d130822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20788 q = 0) : d130823 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20788, d130823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20788, d130823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20789 q = 0) : d130824 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20789, d130824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20789, d130824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d20790 q = 0) : d130825 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20790, d130825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20790, d130825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro10930 (p : Pattern) (selected : d20792 p = 0) : d130827 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d17443 q = 0) : d128059 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17443, d128059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10134 q selected
    | true =>
      simp only [d17443, d128059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10135 q selected
  have h2 (q : Pattern) (selected : d17444 q = 0) : d128060 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17444, d128060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17444, d128060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17445 q = 0) : d128061 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17445, d128061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17445, d128061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17446 q = 0) : d128062 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17446, d128062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10135 q selected
    | true =>
      simp only [d17446, d128062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9706 q selected
  have h5 (q : Pattern) (selected : d17447 q = 0) : d128063 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17447, d128063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17447, d128063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17448 q = 0) : d128064 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17448, d128064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17448, d128064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d17449 q = 0) : d128065 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17449, d128065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17449, d128065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d17450 q = 0) : d128079 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17450, d128079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10135 q selected
    | true =>
      simp only [d17450, d128079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9707 q selected
  have h9 (q : Pattern) (selected : d17451 q = 0) : d128080 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17451, d128080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17451, d128080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d17452 q = 0) : d128081 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17452, d128081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17452, d128081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d17453 q = 0) : d128082 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17453, d128082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d17453, d128082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d17454 q = 0) : d128092 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17454, d128092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d17454, d128092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d10501 q = 0) : d101719 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10501, d101719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6775 q selected
    | true =>
      simp only [d10501, d101719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6777 q selected
  have h14 (q : Pattern) (selected : d10502 q = 0) : d101720 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10502, d101720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d10502, d101720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d10503 q = 0) : d101721 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10503, d101721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10503, d101721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d10528 q = 0) : d101740 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10528, d101740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6777 q selected
    | true =>
      simp only [d10528, d101740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6780 q selected
  have h17 (q : Pattern) (selected : d10529 q = 0) : d101741 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10529, d101741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d10529, d101741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d10530 q = 0) : d101742 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10530, d101742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10530, d101742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d10531 q = 0) : d101743 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10531, d101743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d10531, d101743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d10537 q = 0) : d101762 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10537, d101762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6777 q selected
    | true =>
      simp only [d10537, d101762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6781 q selected
  have h21 (q : Pattern) (selected : d10538 q = 0) : d101763 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10538, d101763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d10538, d101763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d10539 q = 0) : d101764 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10539, d101764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10539, d101764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d10540 q = 0) : d101765 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10540, d101765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d10540, d101765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d10541 q = 0) : d101775 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10541, d101775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d10541, d101775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d20792 q = 0) : d130827 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20792, d130827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d20792, d130827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  exact h25 p selected
theorem eqIntro10931 (p : Pattern) (selected : d20795 p = 0) : d130819 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d17450 q = 0) : d128079 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17450, d128079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10135 q selected
    | true =>
      simp only [d17450, d128079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9707 q selected
  have h2 (q : Pattern) (selected : d17451 q = 0) : d128080 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17451, d128080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17451, d128080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17452 q = 0) : d128081 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17452, d128081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17452, d128081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17453 q = 0) : d128082 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17453, d128082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17453, d128082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17458 q = 0) : d128083 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17458, d128083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17458, d128083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10537 q = 0) : d101762 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10537, d101762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6777 q selected
    | true =>
      simp only [d10537, d101762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6781 q selected
  have h7 (q : Pattern) (selected : d10538 q = 0) : d101763 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10538, d101763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10538, d101763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10539 q = 0) : d101764 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10539, d101764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10539, d101764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10540 q = 0) : d101765 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10540, d101765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10540, d101765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d10545 q = 0) : d101766 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10545, d101766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10545, d101766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d20795 q = 0) : d130819 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20795, d130819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20795, d130819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro10932 (p : Pattern) (selected : d20801 p = 0) : d130833 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20793 q = 0) : d130828 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20793, d130828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10930 q selected
    | true =>
      simp only [d20793, d130828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20794 q = 0) : d130829 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20794, d130829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20794, d130829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20796 q = 0) : d130820 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20796, d130820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10931 q selected
    | true =>
      simp only [d20796, d130820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20797 q = 0) : d130821 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20797, d130821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20797, d130821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20798 q = 0) : d130830 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20798, d130830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20798, d130830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20799 q = 0) : d130831 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20799, d130831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20799, d130831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20800 q = 0) : d130832 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20800, d130832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20800, d130832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d20801 q = 0) : d130833 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20801, d130833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20801, d130833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro10933 (p : Pattern) (selected : d20805 p = 0) : d130837 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20796 q = 0) : d130820 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20796, d130820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10931 q selected
    | true =>
      simp only [d20796, d130820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20797 q = 0) : d130821 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20797, d130821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20797, d130821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20802 q = 0) : d130834 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20802, d130834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20802, d130834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20803 q = 0) : d130835 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20803, d130835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20803, d130835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20804 q = 0) : d130836 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20804, d130836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20804, d130836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20805 q = 0) : d130837 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20805, d130837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20805, d130837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10934 (p : Pattern) (selected : d20808 p = 0) : d130840 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d17397 q = 0) : d128059 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17397, d128059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10126 q selected
    | true =>
      simp only [d17397, d128059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10128 q selected
  have h2 (q : Pattern) (selected : d17398 q = 0) : d128060 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17398, d128060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17398, d128060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17399 q = 0) : d128061 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17399, d128061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17399, d128061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17400 q = 0) : d128062 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17400, d128062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10128 q selected
    | true =>
      simp only [d17400, d128062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9697 q selected
  have h5 (q : Pattern) (selected : d17401 q = 0) : d128063 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17401, d128063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17401, d128063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17402 q = 0) : d128064 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17402, d128064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17402, d128064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d17403 q = 0) : d128065 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17403, d128065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17403, d128065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d17472 q = 0) : d128106 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17472, d128106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10128 q selected
    | true =>
      simp only [d17472, d128106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8463 q selected
  have h9 (q : Pattern) (selected : d17473 q = 0) : d128107 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17473, d128107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17473, d128107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d17474 q = 0) : d128108 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17474, d128108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17474, d128108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d17475 q = 0) : d128109 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17475, d128109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d17475, d128109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d17476 q = 0) : d128110 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17476, d128110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d17476, d128110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d10398 q = 0) : d101719 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6760 q selected
    | true =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6763 q selected
  have h14 (q : Pattern) (selected : d10399 q = 0) : d101720 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d10400 q = 0) : d101721 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d10419 q = 0) : d101740 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6763 q selected
    | true =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6765 q selected
  have h17 (q : Pattern) (selected : d10420 q = 0) : d101741 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d10421 q = 0) : d101742 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d10422 q = 0) : d101743 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d10560 q = 0) : d101790 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10560, d101790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6763 q selected
    | true =>
      simp only [d10560, d101790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6786 q selected
  have h21 (q : Pattern) (selected : d10561 q = 0) : d101791 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10561, d101791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d10561, d101791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d10562 q = 0) : d101792 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10562, d101792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10562, d101792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d10563 q = 0) : d101793 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10563, d101793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d10563, d101793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d10564 q = 0) : d101794 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10564, d101794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d10564, d101794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d20808 q = 0) : d130840 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20808, d130840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d20808, d130840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  exact h25 p selected
theorem eqIntro10935 (p : Pattern) (selected : d20814 p = 0) : d130846 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20809 q = 0) : d130841 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20809, d130841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10934 q selected
    | true =>
      simp only [d20809, d130841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20810 q = 0) : d130842 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20810, d130842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20810, d130842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20811 q = 0) : d130843 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20811, d130843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20811, d130843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20812 q = 0) : d130844 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20812, d130844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20812, d130844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20813 q = 0) : d130845 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20813, d130845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20813, d130845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20814 q = 0) : d130846 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20814, d130846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20814, d130846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10936 (p : Pattern) (selected : d20820 p = 0) : d130852 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20791 q = 0) : d130826 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20791, d130826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10927 q selected
    | true =>
      simp only [d20791, d130826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10929 q selected
  have h2 (q : Pattern) (selected : d20806 q = 0) : d130838 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20806, d130838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10932 q selected
    | true =>
      simp only [d20806, d130838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10933 q selected
  have h3 (q : Pattern) (selected : d20807 q = 0) : d130839 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20807, d130839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20807, d130839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20815 q = 0) : d130847 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20815, d130847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10935 q selected
    | true =>
      simp only [d20815, d130847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20816 q = 0) : d130848 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20816, d130848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20816, d130848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20817 q = 0) : d130849 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20817, d130849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20817, d130849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d20818 q = 0) : d130850 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20818, d130850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20818, d130850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d20819 q = 0) : d130851 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20819, d130851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20819, d130851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d20820 q = 0) : d130852 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20820, d130852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20820, d130852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro10937 (p : Pattern) (selected : d20825 p = 0) : d130837 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20785 q = 0) : d130820 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20785, d130820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10928 q selected
    | true =>
      simp only [d20785, d130820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20786 q = 0) : d130821 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20786, d130821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20786, d130821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20822 q = 0) : d130834 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20822, d130834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20822, d130834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20823 q = 0) : d130835 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20823, d130835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20823, d130835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20824 q = 0) : d130836 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20824, d130836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20824, d130836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20825 q = 0) : d130837 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20825, d130837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20825, d130837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10938 (p : Pattern) (selected : d20831 p = 0) : d130859 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20826 q = 0) : d130854 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20826, d130854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10937 q selected
    | true =>
      simp only [d20826, d130854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20827 q = 0) : d130855 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20827, d130855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20827, d130855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20828 q = 0) : d130856 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20828, d130856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20828, d130856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20829 q = 0) : d130857 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20829, d130857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20829, d130857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20830 q = 0) : d130858 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20830, d130858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20830, d130858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20831 q = 0) : d130859 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20831, d130859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20831, d130859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro10939 (p : Pattern) (selected : d20837 p = 0) : d130865 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20821 q = 0) : d130853 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20821, d130853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20821, d130853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10936 q selected
  have h2 (q : Pattern) (selected : d20832 q = 0) : d130860 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20832, d130860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20832, d130860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10938 q selected
  have h3 (q : Pattern) (selected : d20833 q = 0) : d130861 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20833, d130861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20833, d130861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20834 q = 0) : d130862 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d20834, d130862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20834, d130862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20835 q = 0) : d130863 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d20835, d130863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20835, d130863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20836 q = 0) : d130864 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d20836, d130864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20836, d130864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20837 q = 0) : d130865 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d20837, d130865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20837, d130865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro10940 (p : Pattern) (selected : d20843 p = 0) : d130871 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20838 q = 0) : d130866 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d20838, d130866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20838, d130866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10939 q selected
  have h2 (q : Pattern) (selected : d20839 q = 0) : d130867 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d20839, d130867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20839, d130867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20840 q = 0) : d130868 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d20840, d130868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20840, d130868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20841 q = 0) : d130869 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d20841, d130869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20841, d130869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20842 q = 0) : d130870 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d20842, d130870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20842, d130870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20843 q = 0) : d130871 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d20843, d130871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20843, d130871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro10941 (p : Pattern) (selected : d20849 p = 0) : d130877 p = 1 := by
  have h0 (q : Pattern) (selected : d20557 q = 0) : d130620 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d20557, d130620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10862 q selected
    | true =>
      simp only [d20557, d130620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10877 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d20625 q = 0) : d130674 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d20625, d130674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20625, d130674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10892 q selected
  have h3 (q : Pattern) (selected : d20626 q = 0) : d130675 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d20626, d130675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20626, d130675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20697 q = 0) : d130739 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d20697, d130739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20697, d130739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10908 q selected
  have h5 (q : Pattern) (selected : d20698 q = 0) : d130740 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d20698, d130740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20698, d130740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20699 q = 0) : d130741 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d20699, d130741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20699, d130741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d20770 q = 0) : d130805 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d20770, d130805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20770, d130805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10924 q selected
  have h8 (q : Pattern) (selected : d20771 q = 0) : d130806 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d20771, d130806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20771, d130806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d20772 q = 0) : d130807 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d20772, d130807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20772, d130807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d20773 q = 0) : d130808 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d20773, d130808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20773, d130808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d20844 q = 0) : d130872 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d20844, d130872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20844, d130872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10940 q selected
  have h12 (q : Pattern) (selected : d20845 q = 0) : d130873 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d20845, d130873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20845, d130873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d20846 q = 0) : d130874 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d20846, d130874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20846, d130874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d20847 q = 0) : d130875 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d20847, d130875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20847, d130875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d20848 q = 0) : d130876 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d20848, d130876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d20848, d130876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d20849 q = 0) : d130877 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d20849, d130877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d20849, d130877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro10942 (p : Pattern) (selected : d20855 p = 0) : d130883 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20850 q = 0) : d130878 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d20850, d130878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10941 q selected
    | true =>
      simp only [d20850, d130878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20851 q = 0) : d130879 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d20851, d130879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20851, d130879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d20852 q = 0) : d130880 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d20852, d130880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20852, d130880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20853 q = 0) : d130881 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d20853, d130881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20853, d130881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20854 q = 0) : d130882 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d20854, d130882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20854, d130882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20855 q = 0) : d130883 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d20855, d130883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20855, d130883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10943 (p : Pattern) (selected : d20861 p = 0) : d130889 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20856 q = 0) : d130884 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d20856, d130884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10942 q selected
    | true =>
      simp only [d20856, d130884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20857 q = 0) : d130885 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d20857, d130885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20857, d130885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d20858 q = 0) : d130886 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d20858, d130886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20858, d130886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20859 q = 0) : d130887 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d20859, d130887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20859, d130887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20860 q = 0) : d130888 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d20860, d130888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20860, d130888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20861 q = 0) : d130889 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d20861, d130889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20861, d130889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10944 (p : Pattern) (selected : d20867 p = 0) : d130895 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20862 q = 0) : d130890 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d20862, d130890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10943 q selected
    | true =>
      simp only [d20862, d130890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20863 q = 0) : d130891 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d20863, d130891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20863, d130891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d20864 q = 0) : d130892 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d20864, d130892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20864, d130892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20865 q = 0) : d130893 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d20865, d130893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20865, d130893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20866 q = 0) : d130894 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d20866, d130894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20866, d130894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20867 q = 0) : d130895 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d20867, d130895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20867, d130895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10945 (p : Pattern) (selected : d20873 p = 0) : d130901 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20868 q = 0) : d130896 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d20868, d130896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10944 q selected
    | true =>
      simp only [d20868, d130896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20869 q = 0) : d130897 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d20869, d130897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20869, d130897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d20870 q = 0) : d130898 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d20870, d130898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20870, d130898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20871 q = 0) : d130899 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d20871, d130899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20871, d130899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20872 q = 0) : d130900 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d20872, d130900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20872, d130900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20873 q = 0) : d130901 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d20873, d130901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20873, d130901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10946 (p : Pattern) (selected : d20879 p = 0) : d130907 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20874 q = 0) : d130902 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d20874, d130902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10945 q selected
    | true =>
      simp only [d20874, d130902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20875 q = 0) : d130903 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d20875, d130903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20875, d130903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d20876 q = 0) : d130904 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d20876, d130904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20876, d130904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20877 q = 0) : d130905 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d20877, d130905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20877, d130905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20878 q = 0) : d130906 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d20878, d130906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20878, d130906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20879 q = 0) : d130907 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d20879, d130907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20879, d130907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10947 (p : Pattern) (selected : d20885 p = 0) : d130913 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20880 q = 0) : d130908 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d20880, d130908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10946 q selected
    | true =>
      simp only [d20880, d130908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20881 q = 0) : d130909 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d20881, d130909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20881, d130909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d20882 q = 0) : d130910 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d20882, d130910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20882, d130910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20883 q = 0) : d130911 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d20883, d130911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20883, d130911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20884 q = 0) : d130912 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d20884, d130912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20884, d130912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20885 q = 0) : d130913 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d20885, d130913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20885, d130913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10948 (p : Pattern) (selected : d20891 p = 0) : d130919 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d20886 q = 0) : d130914 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d20886, d130914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10947 q selected
    | true =>
      simp only [d20886, d130914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20887 q = 0) : d130915 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d20887, d130915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20887, d130915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d20888 q = 0) : d130916 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d20888, d130916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20888, d130916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20889 q = 0) : d130917 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d20889, d130917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20889, d130917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20890 q = 0) : d130918 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d20890, d130918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20890, d130918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20891 q = 0) : d130919 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d20891, d130919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20891, d130919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10949 (p : Pattern) (selected : d20421 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d251 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9 q selected
    | true =>
      simp only [d251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d252 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d253 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d254 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d255 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9348 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6802 q selected
    | true =>
      simp only [d9348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d9349 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9350 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d9351 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d9352 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d9352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d20421 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro10950 (p : Pattern) (selected : d20427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20422 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10949 q selected
    | true =>
      simp only [d20422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20423 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20424 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20425 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20426 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20427 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10951 (p : Pattern) (selected : d20433 p = 1) : d130924 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20420 q = 1) : d20420 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d20428 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10950 q selected
    | true =>
      simp only [d20428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d20429 q = 1) : d130920 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20429, d130920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20429, d130920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20398 q = 1) : d20398 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d20430 q = 1) : d130921 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20430, d130921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20430, d130921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20431 q = 1) : d130922 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20431, d130922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20431, d130922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d20432 q = 1) : d130923 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20432, d130923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20432, d130923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d20433 q = 1) : d130924 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20433, d130924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20433, d130924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro10952 (p : Pattern) (selected : d20439 p = 1) : d130930 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20434 q = 1) : d130925 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20434, d130925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20434, d130925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10951 q selected
  have h2 (q : Pattern) (selected : d20435 q = 1) : d130926 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20435, d130926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20435, d130926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d20436 q = 1) : d130927 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d20436, d130927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20436, d130927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20437 q = 1) : d130928 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d20437, d130928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20437, d130928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20438 q = 1) : d130929 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d20438, d130929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20438, d130929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20439 q = 1) : d130930 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d20439, d130930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20439, d130930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro10953 (p : Pattern) (selected : d20453 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d437 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23 q selected
    | true =>
      simp only [d437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9 q selected
  have h2 (q : Pattern) (selected : d438 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d439 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d251 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9 q selected
    | true =>
      simp only [d251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d252 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d253 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d440 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d254 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d441 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d9407 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6807 q selected
    | true =>
      simp only [d9407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6802 q selected
  have h11 (q : Pattern) (selected : d9408 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d9408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d9409 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d9348 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6802 q selected
    | true =>
      simp only [d9348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d9349 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d9349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d9350 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d9410 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d9410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d9351 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d9351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d9411 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d9411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d20453 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d20453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro10954 (p : Pattern) (selected : d20459 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20454 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10953 q selected
    | true =>
      simp only [d20454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20455 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20422 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10949 q selected
    | true =>
      simp only [d20422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20423 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20456 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20457 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20458 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d20459 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro10955 (p : Pattern) (selected : d20471 p = 1) : d130940 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20452 q = 1) : d20452 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d20460 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10954 q selected
    | true =>
      simp only [d20460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10950 q selected
  have h3 (q : Pattern) (selected : d20461 q = 1) : d130936 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20461, d130936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20461, d130936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20467 q = 1) : d20467 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d20468 q = 1) : d130937 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20468, d130937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20468, d130937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20469 q = 1) : d130938 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20469, d130938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20469, d130938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d20470 q = 1) : d130939 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20470, d130939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20470, d130939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d20471 q = 1) : d130940 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20471, d130940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20471, d130940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro10956 (p : Pattern) (selected : d20483 p = 1) : d130946 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20472 q = 1) : d130941 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20472, d130941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20472, d130941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10955 q selected
  have h2 (q : Pattern) (selected : d20478 q = 1) : d20478 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d20479 q = 1) : d130942 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20479, d130942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20479, d130942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20480 q = 1) : d130943 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d20480, d130943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20480, d130943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20481 q = 1) : d130944 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d20481, d130944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20481, d130944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20482 q = 1) : d130945 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d20482, d130945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20482, d130945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20483 q = 1) : d130946 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d20483, d130946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20483, d130946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro10957 (p : Pattern) (selected : d20489 p = 1) : d130952 p = 1 := by
  have h0 (q : Pattern) (selected : d20412 q = 1) : d20412 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d20440 q = 1) : d130931 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d20440, d130931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20440, d130931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10952 q selected
  have h3 (q : Pattern) (selected : d20441 q = 1) : d130932 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d20441, d130932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20441, d130932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20442 q = 1) : d130933 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d20442, d130933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20442, d130933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20443 q = 1) : d130934 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d20443, d130934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20443, d130934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20444 q = 1) : d130935 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d20444, d130935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20444, d130935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d20484 q = 1) : d130947 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d20484, d130947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20484, d130947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10956 q selected
  have h8 (q : Pattern) (selected : d20485 q = 1) : d130948 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d20485, d130948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20485, d130948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d20486 q = 1) : d130949 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d20486, d130949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20486, d130949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d20487 q = 1) : d130950 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d20487, d130950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20487, d130950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d20488 q = 1) : d130951 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d20488, d130951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20488, d130951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d20489 q = 1) : d130952 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d20489, d130952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20489, d130952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro10958 (p : Pattern) (selected : d20508 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d16190 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10168 q selected
    | true =>
      simp only [d16190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23 q selected
  have h2 (q : Pattern) (selected : d16191 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d16192 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d437 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23 q selected
    | true =>
      simp only [d437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9 q selected
  have h5 (q : Pattern) (selected : d438 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d439 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d16193 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d16193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d701 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d16194 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d16194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d9519 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6814 q selected
    | true =>
      simp only [d9519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6807 q selected
  have h11 (q : Pattern) (selected : d9520 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d9520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d9521 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d9407 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6807 q selected
    | true =>
      simp only [d9407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6802 q selected
  have h14 (q : Pattern) (selected : d9408 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d9408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d9409 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d9522 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d9522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d9523 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d9523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d9524 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d9524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d20508 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d20508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro10959 (p : Pattern) (selected : d20511 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d437 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23 q selected
    | true =>
      simp only [d437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9 q selected
  have h2 (q : Pattern) (selected : d438 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d439 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d701 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d706 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9407 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6807 q selected
    | true =>
      simp only [d9407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6802 q selected
  have h7 (q : Pattern) (selected : d9408 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9409 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d9523 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d9528 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d9528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d20511 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro10960 (p : Pattern) (selected : d20517 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20509 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10958 q selected
    | true =>
      simp only [d20509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20510 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20512 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10959 q selected
    | true =>
      simp only [d20512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20513 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20514 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20515 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20516 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d20517 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro10961 (p : Pattern) (selected : d20521 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20512 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10959 q selected
    | true =>
      simp only [d20512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20513 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20518 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20519 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20520 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20521 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10962 (p : Pattern) (selected : d20533 p = 1) : d130957 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20507 q = 1) : d20507 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d20522 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10960 q selected
    | true =>
      simp only [d20522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10961 q selected
  have h3 (q : Pattern) (selected : d20523 q = 1) : d130953 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20523, d130953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20523, d130953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20529 q = 1) : d20529 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d20530 q = 1) : d130954 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20530, d130954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20530, d130954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20531 q = 1) : d130955 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20531, d130955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20531, d130955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d20532 q = 1) : d130956 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20532, d130956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20532, d130956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d20533 q = 1) : d130957 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20533, d130957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20533, d130957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro10963 (p : Pattern) (selected : d20550 p = 1) : d130963 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20534 q = 1) : d130958 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20534, d130958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20534, d130958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10962 q selected
  have h2 (q : Pattern) (selected : d20545 q = 1) : d20545 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d20546 q = 1) : d130959 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20546, d130959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20546, d130959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20547 q = 1) : d130960 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d20547, d130960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20547, d130960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20548 q = 1) : d130961 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d20548, d130961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20548, d130961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20549 q = 1) : d130962 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d20549, d130962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20549, d130962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20550 q = 1) : d130963 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d20550, d130963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20550, d130963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro10964 (p : Pattern) (selected : d20556 p = 1) : d130969 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20551 q = 1) : d130964 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d20551, d130964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20551, d130964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10963 q selected
  have h2 (q : Pattern) (selected : d20552 q = 1) : d130965 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d20552, d130965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20552, d130965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20553 q = 1) : d130966 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d20553, d130966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20553, d130966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20554 q = 1) : d130967 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d20554, d130967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20554, d130967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20555 q = 1) : d130968 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d20555, d130968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20555, d130968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20556 q = 1) : d130969 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d20556, d130969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20556, d130969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro10965 (p : Pattern) (selected : d20576 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d16400 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10181 q selected
    | true =>
      simp only [d16400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro66 q selected
  have h2 (q : Pattern) (selected : d16401 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d16402 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1030 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro66 q selected
    | true =>
      simp only [d1030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro67 q selected
  have h5 (q : Pattern) (selected : d1031 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1032 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d16403 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d16403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d1034 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d16404 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d16404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d9684 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6825 q selected
    | true =>
      simp only [d9684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6826 q selected
  have h11 (q : Pattern) (selected : d9685 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d9685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d9686 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d9688 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6826 q selected
    | true =>
      simp only [d9688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6827 q selected
  have h14 (q : Pattern) (selected : d9689 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d9689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d9690 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d9691 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d9691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d9692 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d9692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d9693 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d9693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d20576 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d20576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro10966 (p : Pattern) (selected : d20579 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1030 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro66 q selected
    | true =>
      simp only [d1030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro67 q selected
  have h2 (q : Pattern) (selected : d1031 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1032 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1034 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1039 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9688 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6826 q selected
    | true =>
      simp only [d9688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6827 q selected
  have h7 (q : Pattern) (selected : d9689 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9690 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d9692 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d9697 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d9697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d20579 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro10967 (p : Pattern) (selected : d20585 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20577 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10965 q selected
    | true =>
      simp only [d20577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20578 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10966 q selected
    | true =>
      simp only [d20580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20581 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20582 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20583 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20584 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d20585 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro10968 (p : Pattern) (selected : d20589 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20580 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10966 q selected
    | true =>
      simp only [d20580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20581 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20586 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20587 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20588 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20589 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10969 (p : Pattern) (selected : d20601 p = 1) : d130975 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20575 q = 1) : d20575 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d20590 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10967 q selected
    | true =>
      simp only [d20590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10968 q selected
  have h3 (q : Pattern) (selected : d20591 q = 1) : d130971 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20591, d130971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20591, d130971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20597 q = 1) : d20597 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d20598 q = 1) : d130972 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20598, d130972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20598, d130972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20599 q = 1) : d130973 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20599, d130973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20599, d130973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d20600 q = 1) : d130974 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20600, d130974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20600, d130974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d20601 q = 1) : d130975 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20601, d130975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20601, d130975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro10970 (p : Pattern) (selected : d20618 p = 1) : d130981 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20602 q = 1) : d130976 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20602, d130976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20602, d130976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10969 q selected
  have h2 (q : Pattern) (selected : d20613 q = 1) : d20613 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d20614 q = 1) : d130977 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20614, d130977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20614, d130977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20615 q = 1) : d130978 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d20615, d130978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20615, d130978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20616 q = 1) : d130979 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d20616, d130979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20616, d130979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20617 q = 1) : d130980 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d20617, d130980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20617, d130980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20618 q = 1) : d130981 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d20618, d130981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20618, d130981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro10971 (p : Pattern) (selected : d20624 p = 1) : d130987 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20619 q = 1) : d130982 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d20619, d130982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20619, d130982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10970 q selected
  have h2 (q : Pattern) (selected : d20620 q = 1) : d130983 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d20620, d130983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20620, d130983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20621 q = 1) : d130984 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d20621, d130984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20621, d130984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20622 q = 1) : d130985 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d20622, d130985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20622, d130985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20623 q = 1) : d130986 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d20623, d130986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20623, d130986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20624 q = 1) : d130987 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d20624, d130987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20624, d130987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro10972 (p : Pattern) (selected : d20645 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d16714 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10198 q selected
    | true =>
      simp only [d16714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10199 q selected
  have h2 (q : Pattern) (selected : d16715 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d16716 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d16717 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10199 q selected
    | true =>
      simp only [d16717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9798 q selected
  have h5 (q : Pattern) (selected : d16718 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d16719 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d16720 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d16720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d16721 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10199 q selected
    | true =>
      simp only [d16721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9799 q selected
  have h9 (q : Pattern) (selected : d16722 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d16723 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d16724 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d16724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d16725 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d16725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d9934 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6840 q selected
    | true =>
      simp only [d9934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6841 q selected
  have h14 (q : Pattern) (selected : d9935 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d9935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d9936 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d9959 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6841 q selected
    | true =>
      simp only [d9959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6844 q selected
  have h17 (q : Pattern) (selected : d9960 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d9960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d9961 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d9962 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d9962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d9965 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6841 q selected
    | true =>
      simp only [d9965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6845 q selected
  have h21 (q : Pattern) (selected : d9966 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d9966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d9967 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d9968 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d9968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d9969 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d9969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d20645 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d20645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  exact h25 p selected
theorem eqIntro10973 (p : Pattern) (selected : d20648 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d16721 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10199 q selected
    | true =>
      simp only [d16721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9799 q selected
  have h2 (q : Pattern) (selected : d16722 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d16723 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d16723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d16724 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d16724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d16729 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d16729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d9965 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6841 q selected
    | true =>
      simp only [d9965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6845 q selected
  have h7 (q : Pattern) (selected : d9966 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d9966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d9967 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d9967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d9968 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d9968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d9973 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d9973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d20648 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro10974 (p : Pattern) (selected : d20654 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20646 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10972 q selected
    | true =>
      simp only [d20646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20647 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20649 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10973 q selected
    | true =>
      simp only [d20649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20650 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20651 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20652 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20653 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d20654 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro10975 (p : Pattern) (selected : d20658 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20649 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10973 q selected
    | true =>
      simp only [d20649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20650 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20655 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20656 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20657 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20658 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10976 (p : Pattern) (selected : d20673 p = 1) : d130994 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20644 q = 1) : d20644 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d20659 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10974 q selected
    | true =>
      simp only [d20659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10975 q selected
  have h3 (q : Pattern) (selected : d20660 q = 1) : d130990 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20660, d130990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20660, d130990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20669 q = 1) : d20669 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d20670 q = 1) : d130991 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20670, d130991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20670, d130991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20671 q = 1) : d130992 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20671, d130992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20671, d130992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d20672 q = 1) : d130993 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20672, d130993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20672, d130993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d20673 q = 1) : d130994 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20673, d130994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20673, d130994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro10977 (p : Pattern) (selected : d20690 p = 1) : d131000 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20674 q = 1) : d130995 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20674, d130995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20674, d130995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10976 q selected
  have h2 (q : Pattern) (selected : d20685 q = 1) : d20685 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d20686 q = 1) : d130996 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20686, d130996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20686, d130996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20687 q = 1) : d130997 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d20687, d130997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20687, d130997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20688 q = 1) : d130998 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d20688, d130998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20688, d130998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20689 q = 1) : d130999 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d20689, d130999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20689, d130999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20690 q = 1) : d131000 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d20690, d131000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20690, d131000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro10978 (p : Pattern) (selected : d20696 p = 1) : d131006 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20691 q = 1) : d131001 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d20691, d131001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20691, d131001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10977 q selected
  have h2 (q : Pattern) (selected : d20692 q = 1) : d131002 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d20692, d131002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20692, d131002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20693 q = 1) : d131003 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d20693, d131003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20693, d131003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20694 q = 1) : d131004 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d20694, d131004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20694, d131004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20695 q = 1) : d131005 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d20695, d131005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20695, d131005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20696 q = 1) : d131006 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d20696, d131006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20696, d131006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro10979 (p : Pattern) (selected : d20718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d17079 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10218 q selected
    | true =>
      simp only [d17079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10219 q selected
  have h2 (q : Pattern) (selected : d17080 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17081 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17082 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10219 q selected
    | true =>
      simp only [d17082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9822 q selected
  have h5 (q : Pattern) (selected : d17083 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17084 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d17085 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d17086 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10219 q selected
    | true =>
      simp only [d17086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9823 q selected
  have h9 (q : Pattern) (selected : d17087 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d17088 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d17089 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d17089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d17090 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d17090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d10234 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6858 q selected
    | true =>
      simp only [d10234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6860 q selected
  have h14 (q : Pattern) (selected : d10235 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d10235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d10236 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d10262 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6860 q selected
    | true =>
      simp only [d10262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6863 q selected
  have h17 (q : Pattern) (selected : d10263 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d10263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d10264 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d10265 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d10265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d10271 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6860 q selected
    | true =>
      simp only [d10271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6864 q selected
  have h21 (q : Pattern) (selected : d10272 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d10272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d10273 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d10274 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d10274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d10275 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d10275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d20718 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d20718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  exact h25 p selected
theorem eqIntro10980 (p : Pattern) (selected : d20721 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d17086 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10219 q selected
    | true =>
      simp only [d17086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9823 q selected
  have h2 (q : Pattern) (selected : d17087 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17088 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17089 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17094 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10271 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6860 q selected
    | true =>
      simp only [d10271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6864 q selected
  have h7 (q : Pattern) (selected : d10272 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10273 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10274 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d10279 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d20721 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro10981 (p : Pattern) (selected : d20727 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20719 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10979 q selected
    | true =>
      simp only [d20719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20720 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20722 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10980 q selected
    | true =>
      simp only [d20722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20724 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20725 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20726 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d20727 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro10982 (p : Pattern) (selected : d20731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20722 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10980 q selected
    | true =>
      simp only [d20722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20723 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20728 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20729 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20730 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20731 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10983 (p : Pattern) (selected : d20746 p = 1) : d131014 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20717 q = 1) : d20717 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d20732 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10981 q selected
    | true =>
      simp only [d20732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10982 q selected
  have h3 (q : Pattern) (selected : d20733 q = 1) : d131010 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20733, d131010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20733, d131010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20742 q = 1) : d20742 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d20743 q = 1) : d131011 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20743, d131011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20743, d131011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20744 q = 1) : d131012 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20744, d131012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20744, d131012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d20745 q = 1) : d131013 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20745, d131013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20745, d131013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d20746 q = 1) : d131014 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20746, d131014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20746, d131014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro10984 (p : Pattern) (selected : d20763 p = 1) : d131020 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20747 q = 1) : d131015 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20747, d131015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20747, d131015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10983 q selected
  have h2 (q : Pattern) (selected : d20758 q = 1) : d20758 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d20759 q = 1) : d131016 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20759, d131016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20759, d131016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20760 q = 1) : d131017 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d20760, d131017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20760, d131017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20761 q = 1) : d131018 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d20761, d131018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20761, d131018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20762 q = 1) : d131019 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d20762, d131019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20762, d131019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20763 q = 1) : d131020 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d20763, d131020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20763, d131020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro10985 (p : Pattern) (selected : d20769 p = 1) : d131026 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20764 q = 1) : d131021 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d20764, d131021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20764, d131021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10984 q selected
  have h2 (q : Pattern) (selected : d20765 q = 1) : d131022 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d20765, d131022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20765, d131022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20766 q = 1) : d131023 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d20766, d131023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20766, d131023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20767 q = 1) : d131024 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d20767, d131024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20767, d131024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20768 q = 1) : d131025 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d20768, d131025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20768, d131025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20769 q = 1) : d131026 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d20769, d131026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20769, d131026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro10986 (p : Pattern) (selected : d20792 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d17443 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10238 q selected
    | true =>
      simp only [d17443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10239 q selected
  have h2 (q : Pattern) (selected : d17444 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17445 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17446 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10239 q selected
    | true =>
      simp only [d17446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9846 q selected
  have h5 (q : Pattern) (selected : d17447 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d17448 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d17449 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d17450 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10239 q selected
    | true =>
      simp only [d17450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9847 q selected
  have h9 (q : Pattern) (selected : d17451 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d17452 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d17453 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d17453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d17454 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d17454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d10501 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6875 q selected
    | true =>
      simp only [d10501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6877 q selected
  have h14 (q : Pattern) (selected : d10502 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d10502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d10503 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d10528 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6877 q selected
    | true =>
      simp only [d10528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6880 q selected
  have h17 (q : Pattern) (selected : d10529 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d10529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d10530 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d10531 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d10531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d10537 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6877 q selected
    | true =>
      simp only [d10537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6881 q selected
  have h21 (q : Pattern) (selected : d10538 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d10538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d10539 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d10540 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d10540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d10541 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d10541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d20792 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d20792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  exact h25 p selected
theorem eqIntro10987 (p : Pattern) (selected : d20795 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d17450 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10239 q selected
    | true =>
      simp only [d17450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro9847 q selected
  have h2 (q : Pattern) (selected : d17451 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d17452 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d17452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d17453 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d17453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d17458 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d17458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10537 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6877 q selected
    | true =>
      simp only [d10537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6881 q selected
  have h7 (q : Pattern) (selected : d10538 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10539 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10540 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d10545 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d20795 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro10988 (p : Pattern) (selected : d20801 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20793 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10986 q selected
    | true =>
      simp only [d20793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20794 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20796 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10987 q selected
    | true =>
      simp only [d20796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20797 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20798 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20799 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20800 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d20801 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d20801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro10989 (p : Pattern) (selected : d20805 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20796 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10987 q selected
    | true =>
      simp only [d20796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20797 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20802 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20803 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20804 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20805 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10990 (p : Pattern) (selected : d20820 p = 1) : d131035 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20791 q = 1) : d20791 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d20806 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10988 q selected
    | true =>
      simp only [d20806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10989 q selected
  have h3 (q : Pattern) (selected : d20807 q = 1) : d131031 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20807, d131031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20807, d131031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20816 q = 1) : d20816 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d20817 q = 1) : d131032 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20817, d131032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20817, d131032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20818 q = 1) : d131033 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20818, d131033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20818, d131033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d20819 q = 1) : d131034 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20819, d131034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20819, d131034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d20820 q = 1) : d131035 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20820, d131035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20820, d131035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro10991 (p : Pattern) (selected : d20837 p = 1) : d131041 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20821 q = 1) : d131036 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20821, d131036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20821, d131036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10990 q selected
  have h2 (q : Pattern) (selected : d20832 q = 1) : d20832 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d20833 q = 1) : d131037 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20833, d131037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20833, d131037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20834 q = 1) : d131038 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d20834, d131038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20834, d131038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20835 q = 1) : d131039 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d20835, d131039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20835, d131039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20836 q = 1) : d131040 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d20836, d131040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20836, d131040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d20837 q = 1) : d131041 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d20837, d131041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20837, d131041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro10992 (p : Pattern) (selected : d20843 p = 1) : d131047 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20838 q = 1) : d131042 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d20838, d131042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20838, d131042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10991 q selected
  have h2 (q : Pattern) (selected : d20839 q = 1) : d131043 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d20839, d131043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20839, d131043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d20840 q = 1) : d131044 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d20840, d131044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20840, d131044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20841 q = 1) : d131045 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d20841, d131045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20841, d131045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d20842 q = 1) : d131046 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d20842, d131046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20842, d131046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20843 q = 1) : d131047 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d20843, d131047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20843, d131047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro10993 (p : Pattern) (selected : d20849 p = 1) : d131053 p = 1 := by
  have h0 (q : Pattern) (selected : d20557 q = 1) : d130970 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d20557, d130970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10957 q selected
    | true =>
      simp only [d20557, d130970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10964 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d20625 q = 1) : d130988 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d20625, d130988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20625, d130988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10971 q selected
  have h3 (q : Pattern) (selected : d20626 q = 1) : d130989 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d20626, d130989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d20626, d130989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d20697 q = 1) : d131007 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d20697, d131007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20697, d131007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10978 q selected
  have h5 (q : Pattern) (selected : d20698 q = 1) : d131008 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d20698, d131008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20698, d131008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d20699 q = 1) : d131009 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d20699, d131009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20699, d131009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d20770 q = 1) : d131027 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d20770, d131027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20770, d131027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10985 q selected
  have h8 (q : Pattern) (selected : d20771 q = 1) : d131028 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d20771, d131028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20771, d131028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d20772 q = 1) : d131029 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d20772, d131029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20772, d131029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d20773 q = 1) : d131030 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d20773, d131030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d20773, d131030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d20844 q = 1) : d131048 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d20844, d131048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20844, d131048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10992 q selected
  have h12 (q : Pattern) (selected : d20845 q = 1) : d131049 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d20845, d131049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20845, d131049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d20846 q = 1) : d131050 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d20846, d131050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20846, d131050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d20847 q = 1) : d131051 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d20847, d131051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20847, d131051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d20848 q = 1) : d131052 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d20848, d131052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d20848, d131052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d20849 q = 1) : d131053 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d20849, d131053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d20849, d131053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro10994 (p : Pattern) (selected : d20855 p = 1) : d131059 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20850 q = 1) : d131054 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d20850, d131054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10993 q selected
    | true =>
      simp only [d20850, d131054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20851 q = 1) : d131055 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d20851, d131055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20851, d131055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d20852 q = 1) : d131056 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d20852, d131056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20852, d131056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20853 q = 1) : d131057 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d20853, d131057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20853, d131057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20854 q = 1) : d131058 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d20854, d131058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20854, d131058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20855 q = 1) : d131059 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d20855, d131059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20855, d131059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10995 (p : Pattern) (selected : d20861 p = 1) : d131065 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20856 q = 1) : d131060 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d20856, d131060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10994 q selected
    | true =>
      simp only [d20856, d131060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20857 q = 1) : d131061 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d20857, d131061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20857, d131061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d20858 q = 1) : d131062 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d20858, d131062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20858, d131062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20859 q = 1) : d131063 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d20859, d131063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20859, d131063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20860 q = 1) : d131064 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d20860, d131064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20860, d131064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20861 q = 1) : d131065 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d20861, d131065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20861, d131065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10996 (p : Pattern) (selected : d20867 p = 1) : d131071 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20862 q = 1) : d131066 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d20862, d131066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10995 q selected
    | true =>
      simp only [d20862, d131066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20863 q = 1) : d131067 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d20863, d131067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20863, d131067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d20864 q = 1) : d131068 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d20864, d131068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20864, d131068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20865 q = 1) : d131069 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d20865, d131069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20865, d131069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20866 q = 1) : d131070 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d20866, d131070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20866, d131070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20867 q = 1) : d131071 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d20867, d131071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20867, d131071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10997 (p : Pattern) (selected : d20873 p = 1) : d131077 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20868 q = 1) : d131072 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d20868, d131072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10996 q selected
    | true =>
      simp only [d20868, d131072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20869 q = 1) : d131073 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d20869, d131073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20869, d131073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d20870 q = 1) : d131074 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d20870, d131074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20870, d131074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20871 q = 1) : d131075 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d20871, d131075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20871, d131075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20872 q = 1) : d131076 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d20872, d131076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20872, d131076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20873 q = 1) : d131077 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d20873, d131077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20873, d131077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10998 (p : Pattern) (selected : d20879 p = 1) : d131083 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20874 q = 1) : d131078 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d20874, d131078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10997 q selected
    | true =>
      simp only [d20874, d131078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20875 q = 1) : d131079 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d20875, d131079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20875, d131079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d20876 q = 1) : d131080 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d20876, d131080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20876, d131080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20877 q = 1) : d131081 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d20877, d131081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20877, d131081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20878 q = 1) : d131082 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d20878, d131082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20878, d131082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20879 q = 1) : d131083 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d20879, d131083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20879, d131083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro10999 (p : Pattern) (selected : d20885 p = 1) : d131089 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d20880 q = 1) : d131084 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d20880, d131084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10998 q selected
    | true =>
      simp only [d20880, d131084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d20881 q = 1) : d131085 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d20881, d131085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d20881, d131085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d20882 q = 1) : d131086 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d20882, d131086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d20882, d131086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d20883 q = 1) : d131087 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d20883, d131087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d20883, d131087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d20884 q = 1) : d131088 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d20884, d131088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d20884, d131088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d20885 q = 1) : d131089 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d20885, d131089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d20885, d131089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
end NetHack.Soko22Hazard87
