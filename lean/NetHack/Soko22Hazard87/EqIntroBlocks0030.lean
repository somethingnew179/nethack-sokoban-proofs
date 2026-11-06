import NetHack.Soko22Hazard87.EqIntroBlocks0029
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro7500 (p : Pattern) (selected : d11065 p = 0) : d107832 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11024 q = 0) : d107808 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11024, d107808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7492 q selected
    | true =>
      simp only [d11024, d107808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11025 q = 0) : d107809 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11025, d107809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11025, d107809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11062 q = 0) : d107829 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11062, d107829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11062, d107829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11063 q = 0) : d107830 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11063, d107830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11063, d107830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11064 q = 0) : d107831 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11064, d107831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11064, d107831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11065 q = 0) : d107832 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11065, d107832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11065, d107832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7501 (p : Pattern) (selected : d11071 p = 0) : d107838 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11038 q = 0) : d107822 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11038, d107822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7493 q selected
    | true =>
      simp only [d11038, d107822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7495 q selected
  have h2 (q : Pattern) (selected : d11060 q = 0) : d107827 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11060, d107827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7498 q selected
    | true =>
      simp only [d11060, d107827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7499 q selected
  have h3 (q : Pattern) (selected : d11061 q = 0) : d107828 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11061, d107828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d11061, d107828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11066 q = 0) : d107833 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11066, d107833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7500 q selected
    | true =>
      simp only [d11066, d107833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11067 q = 0) : d107834 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11067, d107834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11067, d107834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11068 q = 0) : d107835 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11068, d107835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11068, d107835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11069 q = 0) : d107836 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11069, d107836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11069, d107836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11070 q = 0) : d107837 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11070, d107837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11070, d107837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d11071 q = 0) : d107838 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11071, d107838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11071, d107838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7502 (p : Pattern) (selected : d11076 p = 0) : d107826 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11032 q = 0) : d107816 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11032, d107816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7494 q selected
    | true =>
      simp only [d11032, d107816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11033 q = 0) : d107817 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11033, d107817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11033, d107817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11073 q = 0) : d107823 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11073, d107823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11073, d107823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11074 q = 0) : d107824 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11074, d107824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11074, d107824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11075 q = 0) : d107825 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11075, d107825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11075, d107825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11076 q = 0) : d107826 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11076, d107826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11076, d107826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7503 (p : Pattern) (selected : d11082 p = 0) : d107845 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11077 q = 0) : d107840 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11077, d107840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7502 q selected
    | true =>
      simp only [d11077, d107840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11078 q = 0) : d107841 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11078, d107841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11078, d107841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11079 q = 0) : d107842 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11079, d107842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11079, d107842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11080 q = 0) : d107843 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11080, d107843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11080, d107843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11081 q = 0) : d107844 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11081, d107844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11081, d107844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11082 q = 0) : d107845 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11082, d107845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11082, d107845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7504 (p : Pattern) (selected : d11088 p = 0) : d107851 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10886 q = 0) : d107695 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10886, d107695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10886, d107695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7462 q selected
  have h2 (q : Pattern) (selected : d10887 q = 0) : d107696 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10887, d107696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10887, d107696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10896 q = 0) : d107705 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10896, d107705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7462 q selected
    | true =>
      simp only [d10896, d107705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7465 q selected
  have h4 (q : Pattern) (selected : d10897 q = 0) : d107706 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10897, d107706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10897, d107706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10898 q = 0) : d107707 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d10898, d107707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10898, d107707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10986 q = 0) : d107770 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10986, d107770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7477 q selected
    | true =>
      simp only [d10986, d107770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7486 q selected
  have h7 (q : Pattern) (selected : d10999 q = 0) : d107783 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10999, d107783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7487 q selected
    | true =>
      simp only [d10999, d107783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7488 q selected
  have h8 (q : Pattern) (selected : d11000 q = 0) : d107784 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11000, d107784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11000, d107784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d11001 q = 0) : d107785 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11001, d107785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d11001, d107785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d11002 q = 0) : d107786 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d11002, d107786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11002, d107786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d11006 q = 0) : d107790 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11006, d107790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11006, d107790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7489 q selected
  have h12 (q : Pattern) (selected : d11008 q = 0) : d107792 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11008, d107792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11008, d107792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7490 q selected
  have h13 (q : Pattern) (selected : d11009 q = 0) : d107793 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11009, d107793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d11009, d107793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d11010 q = 0) : d107794 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11010, d107794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d11010, d107794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d11011 q = 0) : d107795 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d11011, d107795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d11011, d107795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d11012 q = 0) : d107796 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d11012, d107796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d11012, d107796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d11072 q = 0) : d107839 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11072, d107839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11072, d107839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7501 q selected
  have h18 (q : Pattern) (selected : d11083 q = 0) : d107846 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11083, d107846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11083, d107846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7503 q selected
  have h19 (q : Pattern) (selected : d11084 q = 0) : d107847 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11084, d107847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d11084, d107847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d11085 q = 0) : d107848 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11085, d107848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d11085, d107848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d11086 q = 0) : d107849 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d11086, d107849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d11086, d107849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d11087 q = 0) : d107850 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d11087, d107850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d11087, d107850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d11088 q = 0) : d107851 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d11088, d107851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d11088, d107851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro7505 (p : Pattern) (selected : d11094 p = 0) : d107857 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11089 q = 0) : d107852 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d11089, d107852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11089, d107852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7504 q selected
  have h2 (q : Pattern) (selected : d11090 q = 0) : d107853 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d11090, d107853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11090, d107853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11091 q = 0) : d107854 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d11091, d107854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11091, d107854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11092 q = 0) : d107855 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d11092, d107855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11092, d107855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11093 q = 0) : d107856 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d11093, d107856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11093, d107856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11094 q = 0) : d107857 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d11094, d107857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11094, d107857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7506 (p : Pattern) (selected : d11105 p = 0) : d107868 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11096 q = 0) : d107859 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11096, d107859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro318 q selected
    | true =>
      simp only [d11096, d107859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11097 q = 0) : d107860 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11097, d107860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11097, d107860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11098 q = 0) : d107861 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11098, d107861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11098, d107861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11099 q = 0) : d107862 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11099, d107862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro319 q selected
    | true =>
      simp only [d11099, d107862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11100 q = 0) : d107863 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11100, d107863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11100, d107863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11101 q = 0) : d107864 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11101, d107864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11101, d107864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11102 q = 0) : d107865 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11102, d107865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11102, d107865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11103 q = 0) : d107866 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11103, d107866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11103, d107866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11104 q = 0) : d107867 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11104, d107867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11104, d107867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11105 q = 0) : d107868 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11105, d107868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d11105, d107868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro7507 (p : Pattern) (selected : d11109 p = 0) : d107872 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11099 q = 0) : d107862 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11099, d107862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro319 q selected
    | true =>
      simp only [d11099, d107862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11100 q = 0) : d107863 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11100, d107863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11100, d107863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11101 q = 0) : d107864 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11101, d107864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11101, d107864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11103 q = 0) : d107866 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11103, d107866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11103, d107866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11108 q = 0) : d107871 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11108, d107871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11108, d107871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11109 q = 0) : d107872 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11109, d107872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11109, d107872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7508 (p : Pattern) (selected : d11115 p = 0) : d107878 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11106 q = 0) : d107869 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d107869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7506 q selected
    | true =>
      simp only [d11106, d107869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11107 q = 0) : d107870 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d107870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11107, d107870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11110 q = 0) : d107873 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7507 q selected
    | true =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11111 q = 0) : d107874 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11112 q = 0) : d107875 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d107875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11112, d107875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11113 q = 0) : d107876 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11113, d107876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11113, d107876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11114 q = 0) : d107877 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11114, d107877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11114, d107877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11115 q = 0) : d107878 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11115, d107878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11115, d107878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7509 (p : Pattern) (selected : d11119 p = 0) : d107882 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11110 q = 0) : d107873 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7507 q selected
    | true =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11111 q = 0) : d107874 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11116 q = 0) : d107879 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d107879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11116, d107879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11117 q = 0) : d107880 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11117, d107880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11117, d107880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11118 q = 0) : d107881 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11118, d107881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11118, d107881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11119 q = 0) : d107882 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11119, d107882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11119, d107882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7510 (p : Pattern) (selected : d11125 p = 0) : d107888 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11120 q = 0) : d107883 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11120, d107883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7508 q selected
    | true =>
      simp only [d11120, d107883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7509 q selected
  have h2 (q : Pattern) (selected : d11121 q = 0) : d107884 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11121, d107884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11121, d107884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11122 q = 0) : d107885 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11122, d107885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11122, d107885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11123 q = 0) : d107886 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11123, d107886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11123, d107886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11124 q = 0) : d107887 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11124, d107887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11124, d107887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11125 q = 0) : d107888 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11125, d107888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11125, d107888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7511 (p : Pattern) (selected : d11128 p = 0) : d107891 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11106 q = 0) : d107869 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d107869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7506 q selected
    | true =>
      simp only [d11106, d107869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11107 q = 0) : d107870 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d107870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11107, d107870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11110 q = 0) : d107873 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7507 q selected
    | true =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11111 q = 0) : d107874 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11112 q = 0) : d107875 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d107875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11112, d107875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11113 q = 0) : d107876 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11113, d107876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11113, d107876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11114 q = 0) : d107877 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11114, d107877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11114, d107877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11128 q = 0) : d107891 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11128, d107891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11128, d107891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7512 (p : Pattern) (selected : d11129 p = 0) : d107892 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11110 q = 0) : d107873 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7507 q selected
    | true =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11111 q = 0) : d107874 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11116 q = 0) : d107879 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d107879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11116, d107879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11117 q = 0) : d107880 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11117, d107880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11117, d107880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11118 q = 0) : d107881 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11118, d107881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11118, d107881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11129 q = 0) : d107892 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11129, d107892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11129, d107892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7513 (p : Pattern) (selected : d11135 p = 0) : d107898 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11120 q = 0) : d107883 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11120, d107883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7508 q selected
    | true =>
      simp only [d11120, d107883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7509 q selected
  have h2 (q : Pattern) (selected : d11121 q = 0) : d107884 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11121, d107884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11121, d107884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11122 q = 0) : d107885 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11122, d107885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11122, d107885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11123 q = 0) : d107886 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11123, d107886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11123, d107886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11124 q = 0) : d107887 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11124, d107887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11124, d107887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11130 q = 0) : d107893 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11130, d107893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7511 q selected
    | true =>
      simp only [d11130, d107893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7512 q selected
  have h7 (q : Pattern) (selected : d11131 q = 0) : d107894 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11131, d107894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11131, d107894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11132 q = 0) : d107895 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11132, d107895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11132, d107895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11133 q = 0) : d107896 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11133, d107896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11133, d107896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11134 q = 0) : d107897 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11134, d107897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11134, d107897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d11135 q = 0) : d107898 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11135, d107898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11135, d107898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro7514 (p : Pattern) (selected : d11140 p = 0) : d107903 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11106 q = 0) : d107869 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d107869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7506 q selected
    | true =>
      simp only [d11106, d107869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11107 q = 0) : d107870 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d107870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11107, d107870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11110 q = 0) : d107873 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7507 q selected
    | true =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11111 q = 0) : d107874 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11112 q = 0) : d107875 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d107875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11112, d107875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11113 q = 0) : d107876 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11113, d107876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11113, d107876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11139 q = 0) : d107902 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11139, d107902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11139, d107902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11140 q = 0) : d107903 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11140, d107903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11140, d107903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7515 (p : Pattern) (selected : d11142 p = 0) : d107905 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11110 q = 0) : d107873 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7507 q selected
    | true =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11111 q = 0) : d107874 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11116 q = 0) : d107879 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d107879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11116, d107879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11117 q = 0) : d107880 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11117, d107880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11117, d107880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11141 q = 0) : d107904 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11141, d107904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11141, d107904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11142 q = 0) : d107905 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11142, d107905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11142, d107905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7516 (p : Pattern) (selected : d11149 p = 0) : d107912 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11106 q = 0) : d107869 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d107869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7506 q selected
    | true =>
      simp only [d11106, d107869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11107 q = 0) : d107870 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d107870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11107, d107870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11110 q = 0) : d107873 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7507 q selected
    | true =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11111 q = 0) : d107874 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11112 q = 0) : d107875 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d107875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11112, d107875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11147 q = 0) : d107910 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11147, d107910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11147, d107910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11148 q = 0) : d107911 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11148, d107911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11148, d107911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11149 q = 0) : d107912 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11149, d107912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11149, d107912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7517 (p : Pattern) (selected : d11152 p = 0) : d107915 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11110 q = 0) : d107873 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7507 q selected
    | true =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11111 q = 0) : d107874 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11116 q = 0) : d107879 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d107879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11116, d107879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11150 q = 0) : d107913 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11150, d107913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11150, d107913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11151 q = 0) : d107914 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11151, d107914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11151, d107914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11152 q = 0) : d107915 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11152, d107915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11152, d107915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7518 (p : Pattern) (selected : d11161 p = 0) : d107924 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11156 q = 0) : d107919 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11156, d107919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro336 q selected
    | true =>
      simp only [d11156, d107919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11157 q = 0) : d107920 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11157, d107920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11157, d107920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11158 q = 0) : d107921 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11158, d107921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11158, d107921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11096 q = 0) : d107859 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11096, d107859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro318 q selected
    | true =>
      simp only [d11096, d107859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11097 q = 0) : d107860 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11097, d107860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11097, d107860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11098 q = 0) : d107861 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11098, d107861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11098, d107861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11159 q = 0) : d107922 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11159, d107922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11159, d107922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11099 q = 0) : d107862 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11099, d107862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro319 q selected
    | true =>
      simp only [d11099, d107862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11100 q = 0) : d107863 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11100, d107863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11100, d107863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11101 q = 0) : d107864 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11101, d107864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11101, d107864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d11102 q = 0) : d107865 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11102, d107865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11102, d107865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d11160 q = 0) : d107923 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11160, d107923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11160, d107923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d11161 q = 0) : d107924 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11161, d107924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d11161, d107924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro7519 (p : Pattern) (selected : d11167 p = 0) : d107930 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11162 q = 0) : d107925 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11162, d107925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7518 q selected
    | true =>
      simp only [d11162, d107925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11163 q = 0) : d107926 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11163, d107926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11163, d107926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11106 q = 0) : d107869 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d107869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7506 q selected
    | true =>
      simp only [d11106, d107869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11107 q = 0) : d107870 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d107870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11107, d107870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11164 q = 0) : d107927 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11164, d107927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11164, d107927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11165 q = 0) : d107928 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11165, d107928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11165, d107928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11166 q = 0) : d107929 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11166, d107929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11166, d107929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11167 q = 0) : d107930 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11167, d107930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11167, d107930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7520 (p : Pattern) (selected : d11178 p = 0) : d107868 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11169 q = 0) : d107859 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11169, d107859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro343 q selected
    | true =>
      simp only [d11169, d107859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11170 q = 0) : d107860 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11170, d107860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11170, d107860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11171 q = 0) : d107861 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11171, d107861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11171, d107861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11172 q = 0) : d107862 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11172, d107862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro344 q selected
    | true =>
      simp only [d11172, d107862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11173 q = 0) : d107863 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11173, d107863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11173, d107863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11174 q = 0) : d107864 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11174, d107864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11174, d107864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11175 q = 0) : d107865 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11175, d107865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11175, d107865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11176 q = 0) : d107866 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11176, d107866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11176, d107866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11177 q = 0) : d107867 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11177, d107867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11177, d107867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11178 q = 0) : d107868 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11178, d107868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d11178, d107868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro7521 (p : Pattern) (selected : d11182 p = 0) : d107872 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11172 q = 0) : d107862 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11172, d107862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro344 q selected
    | true =>
      simp only [d11172, d107862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11173 q = 0) : d107863 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11173, d107863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11173, d107863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11174 q = 0) : d107864 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11174, d107864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11174, d107864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11176 q = 0) : d107866 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11176, d107866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11176, d107866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11181 q = 0) : d107871 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11181, d107871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11181, d107871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11182 q = 0) : d107872 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11182, d107872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11182, d107872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7522 (p : Pattern) (selected : d11188 p = 0) : d107878 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11179 q = 0) : d107869 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11179, d107869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7520 q selected
    | true =>
      simp only [d11179, d107869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11180 q = 0) : d107870 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11180, d107870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11180, d107870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11183 q = 0) : d107873 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11183, d107873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7521 q selected
    | true =>
      simp only [d11183, d107873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11184 q = 0) : d107874 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11184, d107874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11184, d107874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11185 q = 0) : d107875 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11185, d107875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11185, d107875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11186 q = 0) : d107876 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11186, d107876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11186, d107876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11187 q = 0) : d107877 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11187, d107877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11187, d107877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11188 q = 0) : d107878 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11188, d107878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11188, d107878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7523 (p : Pattern) (selected : d11192 p = 0) : d107882 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11183 q = 0) : d107873 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11183, d107873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7521 q selected
    | true =>
      simp only [d11183, d107873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11184 q = 0) : d107874 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11184, d107874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11184, d107874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11189 q = 0) : d107879 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11189, d107879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11189, d107879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11190 q = 0) : d107880 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11190, d107880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11190, d107880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11191 q = 0) : d107881 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11191, d107881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11191, d107881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11192 q = 0) : d107882 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11192, d107882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11192, d107882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7524 (p : Pattern) (selected : d11200 p = 0) : d107938 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11096 q = 0) : d107859 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11096, d107859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro318 q selected
    | true =>
      simp only [d11096, d107859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11097 q = 0) : d107860 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11097, d107860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11097, d107860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11098 q = 0) : d107861 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11098, d107861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11098, d107861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11099 q = 0) : d107862 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11099, d107862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro319 q selected
    | true =>
      simp only [d11099, d107862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11100 q = 0) : d107863 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11100, d107863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11100, d107863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11101 q = 0) : d107864 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11101, d107864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11101, d107864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11102 q = 0) : d107865 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11102, d107865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11102, d107865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11195 q = 0) : d107933 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11195, d107933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3355 q selected
    | true =>
      simp only [d11195, d107933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11196 q = 0) : d107934 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11196, d107934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11196, d107934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11197 q = 0) : d107935 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11197, d107935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11197, d107935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d11198 q = 0) : d107936 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11198, d107936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d11198, d107936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d11199 q = 0) : d107937 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11199, d107937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11199, d107937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d11200 q = 0) : d107938 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11200, d107938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d11200, d107938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro7525 (p : Pattern) (selected : d11206 p = 0) : d107944 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11201 q = 0) : d107939 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11201, d107939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7524 q selected
    | true =>
      simp only [d11201, d107939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11202 q = 0) : d107940 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11202, d107940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11202, d107940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11203 q = 0) : d107941 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11203, d107941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11203, d107941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11204 q = 0) : d107942 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11204, d107942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11204, d107942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11205 q = 0) : d107943 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11205, d107943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11205, d107943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11206 q = 0) : d107944 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11206, d107944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11206, d107944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7526 (p : Pattern) (selected : d11212 p = 0) : d107950 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11143 q = 0) : d107906 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11143, d107906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7514 q selected
    | true =>
      simp only [d11143, d107906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7515 q selected
  have h2 (q : Pattern) (selected : d11144 q = 0) : d107907 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11144, d107907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11144, d107907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11145 q = 0) : d107908 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11145, d107908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11145, d107908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11146 q = 0) : d107909 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11146, d107909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11146, d107909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11153 q = 0) : d107916 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11153, d107916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7516 q selected
    | true =>
      simp only [d11153, d107916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7517 q selected
  have h6 (q : Pattern) (selected : d11154 q = 0) : d107917 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11154, d107917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11154, d107917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11155 q = 0) : d107918 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11155, d107918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11155, d107918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11168 q = 0) : d107931 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11168, d107931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7519 q selected
    | true =>
      simp only [d11168, d107931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7508 q selected
  have h9 (q : Pattern) (selected : d11193 q = 0) : d107883 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11193, d107883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7522 q selected
    | true =>
      simp only [d11193, d107883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7523 q selected
  have h10 (q : Pattern) (selected : d11194 q = 0) : d107932 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11194, d107932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d11194, d107932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d11207 q = 0) : d107945 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11207, d107945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7525 q selected
    | true =>
      simp only [d11207, d107945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d11208 q = 0) : d107946 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11208, d107946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d11208, d107946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d11209 q = 0) : d107947 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11209, d107947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d11209, d107947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d11210 q = 0) : d107948 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11210, d107948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11210, d107948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d11211 q = 0) : d107949 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11211, d107949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11211, d107949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d11212 q = 0) : d107950 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11212, d107950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11212, d107950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro7527 (p : Pattern) (selected : d11213 p = 0) : d107951 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11106 q = 0) : d107869 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d107869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7506 q selected
    | true =>
      simp only [d11106, d107869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11107 q = 0) : d107870 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d107870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11107, d107870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11110 q = 0) : d107873 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7507 q selected
    | true =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11111 q = 0) : d107874 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11112 q = 0) : d107875 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d107875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11112, d107875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11113 q = 0) : d107876 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11113, d107876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11113, d107876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11139 q = 0) : d107902 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11139, d107902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11139, d107902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11213 q = 0) : d107951 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11213, d107951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11213, d107951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7528 (p : Pattern) (selected : d11214 p = 0) : d107952 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11110 q = 0) : d107873 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7507 q selected
    | true =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11111 q = 0) : d107874 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11116 q = 0) : d107879 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d107879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11116, d107879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11117 q = 0) : d107880 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11117, d107880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11117, d107880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11141 q = 0) : d107904 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11141, d107904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11141, d107904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11214 q = 0) : d107952 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11214, d107952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11214, d107952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7529 (p : Pattern) (selected : d11219 p = 0) : d107957 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11106 q = 0) : d107869 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d107869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7506 q selected
    | true =>
      simp only [d11106, d107869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11107 q = 0) : d107870 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d107870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11107, d107870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11110 q = 0) : d107873 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7507 q selected
    | true =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11111 q = 0) : d107874 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11112 q = 0) : d107875 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d107875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11112, d107875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11147 q = 0) : d107910 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11147, d107910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11147, d107910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11148 q = 0) : d107911 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11148, d107911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11148, d107911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11219 q = 0) : d107957 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11219, d107957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11219, d107957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7530 (p : Pattern) (selected : d11220 p = 0) : d107958 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11110 q = 0) : d107873 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7507 q selected
    | true =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11111 q = 0) : d107874 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11116 q = 0) : d107879 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d107879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11116, d107879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11150 q = 0) : d107913 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11150, d107913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11150, d107913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11151 q = 0) : d107914 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11151, d107914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11151, d107914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11220 q = 0) : d107958 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11220, d107958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11220, d107958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7531 (p : Pattern) (selected : d11224 p = 0) : d107962 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11162 q = 0) : d107925 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11162, d107925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7518 q selected
    | true =>
      simp only [d11162, d107925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11163 q = 0) : d107926 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11163, d107926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11163, d107926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11106 q = 0) : d107869 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d107869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7506 q selected
    | true =>
      simp only [d11106, d107869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11107 q = 0) : d107870 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d107870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11107, d107870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11164 q = 0) : d107927 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11164, d107927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11164, d107927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11165 q = 0) : d107928 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11165, d107928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11165, d107928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11166 q = 0) : d107929 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11166, d107929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11166, d107929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11224 q = 0) : d107962 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11224, d107962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11224, d107962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7532 (p : Pattern) (selected : d11226 p = 0) : d107891 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11179 q = 0) : d107869 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11179, d107869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7520 q selected
    | true =>
      simp only [d11179, d107869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11180 q = 0) : d107870 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11180, d107870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11180, d107870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11183 q = 0) : d107873 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11183, d107873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7521 q selected
    | true =>
      simp only [d11183, d107873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11184 q = 0) : d107874 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11184, d107874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11184, d107874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11185 q = 0) : d107875 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11185, d107875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11185, d107875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11186 q = 0) : d107876 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11186, d107876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11186, d107876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11187 q = 0) : d107877 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11187, d107877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11187, d107877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11226 q = 0) : d107891 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11226, d107891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11226, d107891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7533 (p : Pattern) (selected : d11227 p = 0) : d107892 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11183 q = 0) : d107873 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11183, d107873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7521 q selected
    | true =>
      simp only [d11183, d107873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11184 q = 0) : d107874 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11184, d107874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11184, d107874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11189 q = 0) : d107879 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11189, d107879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11189, d107879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11190 q = 0) : d107880 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11190, d107880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11190, d107880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11191 q = 0) : d107881 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11191, d107881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11191, d107881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11227 q = 0) : d107892 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11227, d107892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11227, d107892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7534 (p : Pattern) (selected : d11230 p = 0) : d107965 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11201 q = 0) : d107939 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11201, d107939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7524 q selected
    | true =>
      simp only [d11201, d107939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11202 q = 0) : d107940 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11202, d107940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11202, d107940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11203 q = 0) : d107941 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11203, d107941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11203, d107941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11204 q = 0) : d107942 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11204, d107942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11204, d107942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11205 q = 0) : d107943 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11205, d107943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11205, d107943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11230 q = 0) : d107965 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11230, d107965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11230, d107965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7535 (p : Pattern) (selected : d11236 p = 0) : d107971 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11143 q = 0) : d107906 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11143, d107906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7514 q selected
    | true =>
      simp only [d11143, d107906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7515 q selected
  have h2 (q : Pattern) (selected : d11144 q = 0) : d107907 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11144, d107907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11144, d107907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11145 q = 0) : d107908 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11145, d107908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11145, d107908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11146 q = 0) : d107909 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11146, d107909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11146, d107909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11153 q = 0) : d107916 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11153, d107916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7516 q selected
    | true =>
      simp only [d11153, d107916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7517 q selected
  have h6 (q : Pattern) (selected : d11154 q = 0) : d107917 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11154, d107917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11154, d107917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11155 q = 0) : d107918 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11155, d107918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11155, d107918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11168 q = 0) : d107931 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11168, d107931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7519 q selected
    | true =>
      simp only [d11168, d107931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7508 q selected
  have h9 (q : Pattern) (selected : d11193 q = 0) : d107883 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11193, d107883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7522 q selected
    | true =>
      simp only [d11193, d107883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7523 q selected
  have h10 (q : Pattern) (selected : d11194 q = 0) : d107932 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11194, d107932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d11194, d107932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d11207 q = 0) : d107945 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11207, d107945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7525 q selected
    | true =>
      simp only [d11207, d107945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d11208 q = 0) : d107946 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11208, d107946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d11208, d107946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d11209 q = 0) : d107947 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11209, d107947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d11209, d107947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d11210 q = 0) : d107948 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11210, d107948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11210, d107948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d11211 q = 0) : d107949 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11211, d107949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11211, d107949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d11215 q = 0) : d107953 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11215, d107953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7527 q selected
    | true =>
      simp only [d11215, d107953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7528 q selected
  have h17 (q : Pattern) (selected : d11216 q = 0) : d107954 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11216, d107954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11216, d107954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d11217 q = 0) : d107955 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11217, d107955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d11217, d107955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d11218 q = 0) : d107956 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11218, d107956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11218, d107956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d11221 q = 0) : d107959 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11221, d107959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7529 q selected
    | true =>
      simp only [d11221, d107959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7530 q selected
  have h21 (q : Pattern) (selected : d11222 q = 0) : d107960 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11222, d107960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11222, d107960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d11223 q = 0) : d107961 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11223, d107961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d11223, d107961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d11225 q = 0) : d107963 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11225, d107963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7531 q selected
    | true =>
      simp only [d11225, d107963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7511 q selected
  have h24 (q : Pattern) (selected : d11228 q = 0) : d107893 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11228, d107893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7532 q selected
    | true =>
      simp only [d11228, d107893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7533 q selected
  have h25 (q : Pattern) (selected : d11229 q = 0) : d107964 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11229, d107964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d11229, d107964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d11231 q = 0) : d107966 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11231, d107966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7534 q selected
    | true =>
      simp only [d11231, d107966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d11232 q = 0) : d107967 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11232, d107967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d11232, d107967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d11233 q = 0) : d107968 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11233, d107968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d11233, d107968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d11234 q = 0) : d107969 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11234, d107969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d11234, d107969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d11235 q = 0) : d107970 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11235, d107970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d11235, d107970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d11236 q = 0) : d107971 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11236, d107971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d11236, d107971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro7536 (p : Pattern) (selected : d11243 p = 0) : d107978 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11120 q = 0) : d107883 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11120, d107883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7508 q selected
    | true =>
      simp only [d11120, d107883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7509 q selected
  have h2 (q : Pattern) (selected : d11121 q = 0) : d107884 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11121, d107884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11121, d107884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11122 q = 0) : d107885 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11122, d107885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11122, d107885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11123 q = 0) : d107886 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11123, d107886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11123, d107886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11124 q = 0) : d107887 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11124, d107887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11124, d107887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11238 q = 0) : d107973 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11238, d107973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7509 q selected
    | true =>
      simp only [d11238, d107973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11239 q = 0) : d107974 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11239, d107974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11239, d107974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11240 q = 0) : d107975 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11240, d107975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11240, d107975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11241 q = 0) : d107976 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11241, d107976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11241, d107976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11242 q = 0) : d107977 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11242, d107977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11242, d107977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d11243 q = 0) : d107978 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11243, d107978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11243, d107978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro7537 (p : Pattern) (selected : d11249 p = 0) : d107984 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11238 q = 0) : d107973 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11238, d107973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7509 q selected
    | true =>
      simp only [d11238, d107973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11239 q = 0) : d107974 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11239, d107974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11239, d107974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11240 q = 0) : d107975 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11240, d107975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11240, d107975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11241 q = 0) : d107976 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11241, d107976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11241, d107976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11242 q = 0) : d107977 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11242, d107977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11242, d107977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11244 q = 0) : d107979 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11244, d107979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7512 q selected
    | true =>
      simp only [d11244, d107979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11245 q = 0) : d107980 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11245, d107980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11245, d107980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11246 q = 0) : d107981 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11246, d107981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11246, d107981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11247 q = 0) : d107982 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11247, d107982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11247, d107982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11248 q = 0) : d107983 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11248, d107983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11248, d107983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d11249 q = 0) : d107984 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11249, d107984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11249, d107984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro7538 (p : Pattern) (selected : d11256 p = 0) : d107991 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11225 q = 0) : d107963 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11225, d107963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7531 q selected
    | true =>
      simp only [d11225, d107963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7511 q selected
  have h2 (q : Pattern) (selected : d11228 q = 0) : d107893 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11228, d107893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7532 q selected
    | true =>
      simp only [d11228, d107893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7533 q selected
  have h3 (q : Pattern) (selected : d11229 q = 0) : d107964 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11229, d107964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d11229, d107964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11231 q = 0) : d107966 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11231, d107966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7534 q selected
    | true =>
      simp only [d11231, d107966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11232 q = 0) : d107967 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11232, d107967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11232, d107967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11233 q = 0) : d107968 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11233, d107968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11233, d107968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11254 q = 0) : d107989 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11254, d107989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11254, d107989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11255 q = 0) : d107990 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11255, d107990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11255, d107990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d11256 q = 0) : d107991 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11256, d107991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11256, d107991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7539 (p : Pattern) (selected : d11258 p = 0) : d107993 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11244 q = 0) : d107979 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11244, d107979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7512 q selected
    | true =>
      simp only [d11244, d107979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11245 q = 0) : d107980 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11245, d107980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11245, d107980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11246 q = 0) : d107981 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11246, d107981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11246, d107981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11247 q = 0) : d107982 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11247, d107982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11247, d107982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11248 q = 0) : d107983 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11248, d107983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11248, d107983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11258 q = 0) : d107993 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11258, d107993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11258, d107993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7540 (p : Pattern) (selected : d11276 p = 0) : d108011 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11264 q = 0) : d107999 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11264, d107999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro363 q selected
    | true =>
      simp only [d11264, d107999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11265 q = 0) : d108000 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11265, d108000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11265, d108000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11266 q = 0) : d108001 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11266, d108001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11266, d108001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11267 q = 0) : d108002 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11267, d108002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro364 q selected
    | true =>
      simp only [d11267, d108002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11268 q = 0) : d108003 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11268, d108003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11268, d108003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11269 q = 0) : d108004 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11269, d108004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11269, d108004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11270 q = 0) : d108005 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11270, d108005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11270, d108005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11271 q = 0) : d108006 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11271, d108006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro365 q selected
    | true =>
      simp only [d11271, d108006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11272 q = 0) : d108007 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11272, d108007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11272, d108007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11273 q = 0) : d108008 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11273, d108008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11273, d108008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d11274 q = 0) : d108009 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11274, d108009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11274, d108009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d11275 q = 0) : d108010 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11275, d108010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11275, d108010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d11276 q = 0) : d108011 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11276, d108011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d11276, d108011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro7541 (p : Pattern) (selected : d11281 p = 0) : d108016 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11267 q = 0) : d108002 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11267, d108002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro364 q selected
    | true =>
      simp only [d11267, d108002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11268 q = 0) : d108003 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11268, d108003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11268, d108003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11269 q = 0) : d108004 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11269, d108004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11269, d108004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11271 q = 0) : d108006 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11271, d108006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro365 q selected
    | true =>
      simp only [d11271, d108006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11272 q = 0) : d108007 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11272, d108007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11272, d108007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11273 q = 0) : d108008 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11273, d108008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11273, d108008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11274 q = 0) : d108009 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11274, d108009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11274, d108009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11279 q = 0) : d108014 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11279, d108014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11279, d108014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11280 q = 0) : d108015 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11280, d108015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11280, d108015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11281 q = 0) : d108016 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11281, d108016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d11281, d108016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro7542 (p : Pattern) (selected : d11287 p = 0) : d108022 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11277 q = 0) : d108012 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11277, d108012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7540 q selected
    | true =>
      simp only [d11277, d108012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11278 q = 0) : d108013 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11278, d108013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11278, d108013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11282 q = 0) : d108017 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11282, d108017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7541 q selected
    | true =>
      simp only [d11282, d108017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11283 q = 0) : d108018 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11283, d108018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11283, d108018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11284 q = 0) : d108019 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11284, d108019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11284, d108019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11285 q = 0) : d108020 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11285, d108020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11285, d108020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11286 q = 0) : d108021 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11286, d108021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11286, d108021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11287 q = 0) : d108022 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11287, d108022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11287, d108022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7543 (p : Pattern) (selected : d11289 p = 0) : d108024 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11271 q = 0) : d108006 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11271, d108006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro365 q selected
    | true =>
      simp only [d11271, d108006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11272 q = 0) : d108007 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11272, d108007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11272, d108007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11273 q = 0) : d108008 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11273, d108008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11273, d108008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11279 q = 0) : d108014 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11279, d108014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11279, d108014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11288 q = 0) : d108023 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11288, d108023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11288, d108023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11289 q = 0) : d108024 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11289, d108024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11289, d108024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7544 (p : Pattern) (selected : d11295 p = 0) : d108030 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11282 q = 0) : d108017 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11282, d108017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7541 q selected
    | true =>
      simp only [d11282, d108017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11283 q = 0) : d108018 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11283, d108018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11283, d108018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11290 q = 0) : d108025 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11290, d108025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7543 q selected
    | true =>
      simp only [d11290, d108025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11291 q = 0) : d108026 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11291, d108026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11291, d108026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11292 q = 0) : d108027 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11292, d108027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11292, d108027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11293 q = 0) : d108028 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11293, d108028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11293, d108028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11294 q = 0) : d108029 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11294, d108029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11294, d108029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11295 q = 0) : d108030 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11295, d108030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11295, d108030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7545 (p : Pattern) (selected : d11306 p = 0) : d108016 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11297 q = 0) : d108002 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11297, d108002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro372 q selected
    | true =>
      simp only [d11297, d108002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11298 q = 0) : d108003 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11298, d108003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11298, d108003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11299 q = 0) : d108004 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11299, d108004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11299, d108004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11300 q = 0) : d108006 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11300, d108006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro373 q selected
    | true =>
      simp only [d11300, d108006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11301 q = 0) : d108007 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11301, d108007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11301, d108007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11302 q = 0) : d108008 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11302, d108008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11302, d108008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11303 q = 0) : d108009 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11303, d108009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11303, d108009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11304 q = 0) : d108014 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11304, d108014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11304, d108014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11305 q = 0) : d108015 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11305, d108015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11305, d108015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11306 q = 0) : d108016 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11306, d108016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d11306, d108016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro7546 (p : Pattern) (selected : d11310 p = 0) : d108024 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11300 q = 0) : d108006 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11300, d108006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro373 q selected
    | true =>
      simp only [d11300, d108006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11301 q = 0) : d108007 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11301, d108007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11301, d108007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11302 q = 0) : d108008 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11302, d108008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11302, d108008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11304 q = 0) : d108014 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11304, d108014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11304, d108014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11309 q = 0) : d108023 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11309, d108023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11309, d108023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11310 q = 0) : d108024 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11310, d108024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11310, d108024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7547 (p : Pattern) (selected : d11316 p = 0) : d108030 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11307 q = 0) : d108017 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11307, d108017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7545 q selected
    | true =>
      simp only [d11307, d108017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11308 q = 0) : d108018 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11308, d108018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11308, d108018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11311 q = 0) : d108025 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11311, d108025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7546 q selected
    | true =>
      simp only [d11311, d108025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11312 q = 0) : d108026 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11312, d108026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11312, d108026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11313 q = 0) : d108027 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11313, d108027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11313, d108027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11314 q = 0) : d108028 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11314, d108028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11314, d108028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11315 q = 0) : d108029 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11315, d108029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11315, d108029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11316 q = 0) : d108030 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11316, d108030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11316, d108030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7548 (p : Pattern) (selected : d11320 p = 0) : d108035 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11311 q = 0) : d108025 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11311, d108025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7546 q selected
    | true =>
      simp only [d11311, d108025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11312 q = 0) : d108026 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11312, d108026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11312, d108026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11317 q = 0) : d108032 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11317, d108032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11317, d108032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11318 q = 0) : d108033 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11318, d108033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11318, d108033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11319 q = 0) : d108034 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11319, d108034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11319, d108034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11320 q = 0) : d108035 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11320, d108035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11320, d108035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7549 (p : Pattern) (selected : d11328 p = 0) : d108043 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11267 q = 0) : d108002 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11267, d108002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro364 q selected
    | true =>
      simp only [d11267, d108002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11268 q = 0) : d108003 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11268, d108003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11268, d108003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11269 q = 0) : d108004 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11269, d108004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11269, d108004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11271 q = 0) : d108006 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11271, d108006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro365 q selected
    | true =>
      simp only [d11271, d108006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11272 q = 0) : d108007 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11272, d108007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11272, d108007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11273 q = 0) : d108008 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11273, d108008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11273, d108008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11274 q = 0) : d108009 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11274, d108009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11274, d108009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11323 q = 0) : d108038 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11323, d108038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3363 q selected
    | true =>
      simp only [d11323, d108038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11324 q = 0) : d108039 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11324, d108039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11324, d108039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11325 q = 0) : d108040 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11325, d108040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11325, d108040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d11326 q = 0) : d108041 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11326, d108041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d11326, d108041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d11327 q = 0) : d108042 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11327, d108042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11327, d108042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d11328 q = 0) : d108043 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11328, d108043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d11328, d108043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro7550 (p : Pattern) (selected : d11334 p = 0) : d108049 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11329 q = 0) : d108044 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11329, d108044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7549 q selected
    | true =>
      simp only [d11329, d108044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11330 q = 0) : d108045 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11330, d108045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11330, d108045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11331 q = 0) : d108046 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11331, d108046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11331, d108046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11332 q = 0) : d108047 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11332, d108047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11332, d108047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11333 q = 0) : d108048 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11333, d108048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11333, d108048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11334 q = 0) : d108049 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11334, d108049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11334, d108049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7551 (p : Pattern) (selected : d11340 p = 0) : d108055 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11296 q = 0) : d108031 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11296, d108031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7542 q selected
    | true =>
      simp only [d11296, d108031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7544 q selected
  have h2 (q : Pattern) (selected : d11321 q = 0) : d108036 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11321, d108036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7547 q selected
    | true =>
      simp only [d11321, d108036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7548 q selected
  have h3 (q : Pattern) (selected : d11322 q = 0) : d108037 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11322, d108037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d11322, d108037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11335 q = 0) : d108050 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11335, d108050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7550 q selected
    | true =>
      simp only [d11335, d108050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11336 q = 0) : d108051 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11336, d108051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11336, d108051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11337 q = 0) : d108052 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11337, d108052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11337, d108052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11338 q = 0) : d108053 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11338, d108053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11338, d108053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11339 q = 0) : d108054 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11339, d108054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11339, d108054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d11340 q = 0) : d108055 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11340, d108055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11340, d108055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7552 (p : Pattern) (selected : d11345 p = 0) : d108035 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11290 q = 0) : d108025 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11290, d108025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7543 q selected
    | true =>
      simp only [d11290, d108025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11291 q = 0) : d108026 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11291, d108026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11291, d108026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11342 q = 0) : d108032 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11342, d108032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11342, d108032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11343 q = 0) : d108033 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11343, d108033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11343, d108033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11344 q = 0) : d108034 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11344, d108034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11344, d108034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11345 q = 0) : d108035 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11345, d108035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11345, d108035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7553 (p : Pattern) (selected : d11351 p = 0) : d108062 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11346 q = 0) : d108057 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11346, d108057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7552 q selected
    | true =>
      simp only [d11346, d108057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11347 q = 0) : d108058 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11347, d108058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11347, d108058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11348 q = 0) : d108059 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11348, d108059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11348, d108059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11349 q = 0) : d108060 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11349, d108060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11349, d108060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11350 q = 0) : d108061 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11350, d108061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11350, d108061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11351 q = 0) : d108062 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11351, d108062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11351, d108062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7554 (p : Pattern) (selected : d11357 p = 0) : d108068 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11126 q = 0) : d107889 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11126, d107889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11126, d107889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7510 q selected
  have h2 (q : Pattern) (selected : d11127 q = 0) : d107890 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11127, d107890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d11127, d107890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d11136 q = 0) : d107899 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11136, d107899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7510 q selected
    | true =>
      simp only [d11136, d107899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7513 q selected
  have h4 (q : Pattern) (selected : d11137 q = 0) : d107900 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11137, d107900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11137, d107900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11138 q = 0) : d107901 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11138, d107901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11138, d107901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11237 q = 0) : d107972 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11237, d107972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7526 q selected
    | true =>
      simp only [d11237, d107972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7535 q selected
  have h7 (q : Pattern) (selected : d11250 q = 0) : d107985 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11250, d107985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7536 q selected
    | true =>
      simp only [d11250, d107985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7537 q selected
  have h8 (q : Pattern) (selected : d11251 q = 0) : d107986 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11251, d107986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11251, d107986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d11252 q = 0) : d107987 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11252, d107987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d11252, d107987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d11253 q = 0) : d107988 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d11253, d107988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11253, d107988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d11257 q = 0) : d107992 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11257, d107992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11257, d107992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7538 q selected
  have h12 (q : Pattern) (selected : d11259 q = 0) : d107994 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11259, d107994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11259, d107994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7539 q selected
  have h13 (q : Pattern) (selected : d11260 q = 0) : d107995 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11260, d107995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d11260, d107995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d11261 q = 0) : d107996 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11261, d107996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d11261, d107996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d11262 q = 0) : d107997 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d11262, d107997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d11262, d107997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d11263 q = 0) : d107998 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d11263, d107998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d11263, d107998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d11341 q = 0) : d108056 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11341, d108056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11341, d108056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7551 q selected
  have h18 (q : Pattern) (selected : d11352 q = 0) : d108063 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11352, d108063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11352, d108063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7553 q selected
  have h19 (q : Pattern) (selected : d11353 q = 0) : d108064 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11353, d108064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d11353, d108064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d11354 q = 0) : d108065 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11354, d108065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d11354, d108065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d11355 q = 0) : d108066 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d11355, d108066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d11355, d108066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d11356 q = 0) : d108067 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d11356, d108067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d11356, d108067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d11357 q = 0) : d108068 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d11357, d108068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d11357, d108068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro7555 (p : Pattern) (selected : d11363 p = 0) : d108074 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11358 q = 0) : d108069 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d11358, d108069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11358, d108069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7554 q selected
  have h2 (q : Pattern) (selected : d11359 q = 0) : d108070 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d11359, d108070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11359, d108070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11360 q = 0) : d108071 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d11360, d108071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11360, d108071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11361 q = 0) : d108072 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d11361, d108072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11361, d108072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11362 q = 0) : d108073 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d11362, d108073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11362, d108073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11363 q = 0) : d108074 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d11363, d108074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11363, d108074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7556 (p : Pattern) (selected : d11375 p = 0) : d108086 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11366 q = 0) : d108077 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11366, d108077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro389 q selected
    | true =>
      simp only [d11366, d108077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11367 q = 0) : d108078 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11367, d108078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11367, d108078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11368 q = 0) : d108079 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11368, d108079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11368, d108079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11369 q = 0) : d108080 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11369, d108080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro390 q selected
    | true =>
      simp only [d11369, d108080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11370 q = 0) : d108081 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11370, d108081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11370, d108081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11371 q = 0) : d108082 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11371, d108082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11371, d108082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11372 q = 0) : d108083 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11372, d108083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11372, d108083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11373 q = 0) : d108084 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11373, d108084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11373, d108084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11374 q = 0) : d108085 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11374, d108085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11374, d108085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11375 q = 0) : d108086 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11375, d108086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d11375, d108086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro7557 (p : Pattern) (selected : d11379 p = 0) : d108090 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11369 q = 0) : d108080 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11369, d108080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro390 q selected
    | true =>
      simp only [d11369, d108080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11370 q = 0) : d108081 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11370, d108081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11370, d108081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11371 q = 0) : d108082 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11371, d108082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11371, d108082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11373 q = 0) : d108084 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11373, d108084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11373, d108084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11378 q = 0) : d108089 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11378, d108089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11378, d108089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11379 q = 0) : d108090 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11379, d108090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11379, d108090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7558 (p : Pattern) (selected : d11385 p = 0) : d108096 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11376 q = 0) : d108087 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d108087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7556 q selected
    | true =>
      simp only [d11376, d108087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11377 q = 0) : d108088 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d108088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11377, d108088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11380 q = 0) : d108091 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d108091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7557 q selected
    | true =>
      simp only [d11380, d108091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11381 q = 0) : d108092 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d108092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11381, d108092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11382 q = 0) : d108093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d108093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11382, d108093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11383 q = 0) : d108094 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11383, d108094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11383, d108094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11384 q = 0) : d108095 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11384, d108095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11384, d108095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11385 q = 0) : d108096 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11385, d108096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11385, d108096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7559 (p : Pattern) (selected : d11389 p = 0) : d108100 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11380 q = 0) : d108091 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d108091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7557 q selected
    | true =>
      simp only [d11380, d108091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11381 q = 0) : d108092 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d108092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11381, d108092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11386 q = 0) : d108097 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11386, d108097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11386, d108097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11387 q = 0) : d108098 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11387, d108098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11387, d108098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11388 q = 0) : d108099 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11388, d108099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11388, d108099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11389 q = 0) : d108100 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11389, d108100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11389, d108100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7560 (p : Pattern) (selected : d11395 p = 0) : d108106 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11390 q = 0) : d108101 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11390, d108101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7558 q selected
    | true =>
      simp only [d11390, d108101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7559 q selected
  have h2 (q : Pattern) (selected : d11391 q = 0) : d108102 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11391, d108102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11391, d108102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11392 q = 0) : d108103 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11392, d108103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11392, d108103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11393 q = 0) : d108104 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11393, d108104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11393, d108104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11394 q = 0) : d108105 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11394, d108105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11394, d108105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11395 q = 0) : d108106 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11395, d108106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11395, d108106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7561 (p : Pattern) (selected : d11398 p = 0) : d108109 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11376 q = 0) : d108087 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d108087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7556 q selected
    | true =>
      simp only [d11376, d108087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11377 q = 0) : d108088 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d108088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11377, d108088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11380 q = 0) : d108091 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d108091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7557 q selected
    | true =>
      simp only [d11380, d108091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11381 q = 0) : d108092 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d108092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11381, d108092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11382 q = 0) : d108093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d108093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11382, d108093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11383 q = 0) : d108094 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11383, d108094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11383, d108094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11384 q = 0) : d108095 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11384, d108095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11384, d108095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11398 q = 0) : d108109 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11398, d108109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11398, d108109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7562 (p : Pattern) (selected : d11399 p = 0) : d108110 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11380 q = 0) : d108091 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d108091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7557 q selected
    | true =>
      simp only [d11380, d108091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11381 q = 0) : d108092 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d108092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11381, d108092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11386 q = 0) : d108097 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11386, d108097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11386, d108097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11387 q = 0) : d108098 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11387, d108098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11387, d108098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11388 q = 0) : d108099 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11388, d108099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11388, d108099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11399 q = 0) : d108110 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11399, d108110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11399, d108110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7563 (p : Pattern) (selected : d11405 p = 0) : d108116 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11390 q = 0) : d108101 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11390, d108101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7558 q selected
    | true =>
      simp only [d11390, d108101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7559 q selected
  have h2 (q : Pattern) (selected : d11391 q = 0) : d108102 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11391, d108102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11391, d108102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11392 q = 0) : d108103 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11392, d108103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11392, d108103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11393 q = 0) : d108104 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11393, d108104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11393, d108104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11394 q = 0) : d108105 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11394, d108105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11394, d108105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11400 q = 0) : d108111 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11400, d108111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7561 q selected
    | true =>
      simp only [d11400, d108111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7562 q selected
  have h7 (q : Pattern) (selected : d11401 q = 0) : d108112 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11401, d108112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11401, d108112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11402 q = 0) : d108113 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11402, d108113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11402, d108113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11403 q = 0) : d108114 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11403, d108114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11403, d108114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11404 q = 0) : d108115 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11404, d108115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11404, d108115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d11405 q = 0) : d108116 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11405, d108116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11405, d108116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro7564 (p : Pattern) (selected : d11410 p = 0) : d108121 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11376 q = 0) : d108087 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d108087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7556 q selected
    | true =>
      simp only [d11376, d108087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11377 q = 0) : d108088 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d108088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11377, d108088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11380 q = 0) : d108091 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d108091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7557 q selected
    | true =>
      simp only [d11380, d108091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11381 q = 0) : d108092 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d108092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11381, d108092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11382 q = 0) : d108093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d108093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11382, d108093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11383 q = 0) : d108094 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11383, d108094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11383, d108094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11409 q = 0) : d108120 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11409, d108120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11409, d108120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11410 q = 0) : d108121 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11410, d108121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11410, d108121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7565 (p : Pattern) (selected : d11412 p = 0) : d108123 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11380 q = 0) : d108091 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d108091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7557 q selected
    | true =>
      simp only [d11380, d108091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11381 q = 0) : d108092 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d108092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11381, d108092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11386 q = 0) : d108097 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11386, d108097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11386, d108097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11387 q = 0) : d108098 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11387, d108098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11387, d108098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11411 q = 0) : d108122 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11411, d108122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11411, d108122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11412 q = 0) : d108123 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11412, d108123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11412, d108123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7566 (p : Pattern) (selected : d11419 p = 0) : d108130 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11376 q = 0) : d108087 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d108087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7556 q selected
    | true =>
      simp only [d11376, d108087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11377 q = 0) : d108088 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d108088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11377, d108088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11380 q = 0) : d108091 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d108091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7557 q selected
    | true =>
      simp only [d11380, d108091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11381 q = 0) : d108092 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d108092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11381, d108092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11382 q = 0) : d108093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d108093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11382, d108093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11417 q = 0) : d108128 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11417, d108128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11417, d108128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11418 q = 0) : d108129 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11418, d108129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11418, d108129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11419 q = 0) : d108130 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11419, d108130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11419, d108130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7567 (p : Pattern) (selected : d11422 p = 0) : d108133 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11380 q = 0) : d108091 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d108091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7557 q selected
    | true =>
      simp only [d11380, d108091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11381 q = 0) : d108092 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d108092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11381, d108092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11386 q = 0) : d108097 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11386, d108097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11386, d108097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11420 q = 0) : d108131 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11420, d108131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11420, d108131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11421 q = 0) : d108132 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11421, d108132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11421, d108132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11422 q = 0) : d108133 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11422, d108133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11422, d108133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7568 (p : Pattern) (selected : d11431 p = 0) : d108142 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11426 q = 0) : d108137 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11426, d108137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro408 q selected
    | true =>
      simp only [d11426, d108137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11427 q = 0) : d108138 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11427, d108138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11427, d108138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11428 q = 0) : d108139 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11428, d108139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11428, d108139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11366 q = 0) : d108077 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11366, d108077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro389 q selected
    | true =>
      simp only [d11366, d108077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11367 q = 0) : d108078 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11367, d108078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11367, d108078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11368 q = 0) : d108079 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11368, d108079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11368, d108079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11429 q = 0) : d108140 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11429, d108140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11429, d108140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11369 q = 0) : d108080 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11369, d108080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro390 q selected
    | true =>
      simp only [d11369, d108080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11370 q = 0) : d108081 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11370, d108081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11370, d108081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11371 q = 0) : d108082 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11371, d108082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11371, d108082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d11372 q = 0) : d108083 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11372, d108083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11372, d108083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d11430 q = 0) : d108141 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11430, d108141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11430, d108141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d11431 q = 0) : d108142 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11431, d108142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d11431, d108142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro7569 (p : Pattern) (selected : d11437 p = 0) : d108148 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11432 q = 0) : d108143 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11432, d108143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7568 q selected
    | true =>
      simp only [d11432, d108143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11433 q = 0) : d108144 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11433, d108144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11433, d108144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11376 q = 0) : d108087 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d108087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7556 q selected
    | true =>
      simp only [d11376, d108087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11377 q = 0) : d108088 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d108088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11377, d108088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11434 q = 0) : d108145 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11434, d108145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11434, d108145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11435 q = 0) : d108146 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11435, d108146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11435, d108146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11436 q = 0) : d108147 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11436, d108147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11436, d108147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11437 q = 0) : d108148 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11437, d108148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11437, d108148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7570 (p : Pattern) (selected : d11448 p = 0) : d108086 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11439 q = 0) : d108077 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11439, d108077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro418 q selected
    | true =>
      simp only [d11439, d108077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11440 q = 0) : d108078 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11440, d108078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11440, d108078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11441 q = 0) : d108079 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11441, d108079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11441, d108079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11442 q = 0) : d108080 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11442, d108080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro419 q selected
    | true =>
      simp only [d11442, d108080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11443 q = 0) : d108081 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11443, d108081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11443, d108081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11444 q = 0) : d108082 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11444, d108082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11444, d108082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11445 q = 0) : d108083 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11445, d108083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11445, d108083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11446 q = 0) : d108084 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11446, d108084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11446, d108084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11447 q = 0) : d108085 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11447, d108085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11447, d108085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11448 q = 0) : d108086 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11448, d108086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d11448, d108086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro7571 (p : Pattern) (selected : d11452 p = 0) : d108090 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11442 q = 0) : d108080 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11442, d108080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro419 q selected
    | true =>
      simp only [d11442, d108080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11443 q = 0) : d108081 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11443, d108081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11443, d108081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11444 q = 0) : d108082 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11444, d108082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11444, d108082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11446 q = 0) : d108084 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11446, d108084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11446, d108084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11451 q = 0) : d108089 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11451, d108089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11451, d108089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11452 q = 0) : d108090 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11452, d108090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11452, d108090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7572 (p : Pattern) (selected : d11458 p = 0) : d108096 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11449 q = 0) : d108087 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11449, d108087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7570 q selected
    | true =>
      simp only [d11449, d108087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11450 q = 0) : d108088 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11450, d108088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11450, d108088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11453 q = 0) : d108091 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11453, d108091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7571 q selected
    | true =>
      simp only [d11453, d108091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11454 q = 0) : d108092 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11454, d108092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11454, d108092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11455 q = 0) : d108093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11455, d108093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11455, d108093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11456 q = 0) : d108094 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11456, d108094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11456, d108094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11457 q = 0) : d108095 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11457, d108095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11457, d108095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11458 q = 0) : d108096 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11458, d108096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11458, d108096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7573 (p : Pattern) (selected : d11462 p = 0) : d108100 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11453 q = 0) : d108091 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11453, d108091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7571 q selected
    | true =>
      simp only [d11453, d108091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11454 q = 0) : d108092 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11454, d108092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11454, d108092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11459 q = 0) : d108097 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11459, d108097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11459, d108097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11460 q = 0) : d108098 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11460, d108098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11460, d108098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11461 q = 0) : d108099 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11461, d108099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11461, d108099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11462 q = 0) : d108100 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11462, d108100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11462, d108100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7574 (p : Pattern) (selected : d11470 p = 0) : d108156 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11366 q = 0) : d108077 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11366, d108077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro389 q selected
    | true =>
      simp only [d11366, d108077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11367 q = 0) : d108078 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11367, d108078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11367, d108078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11368 q = 0) : d108079 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11368, d108079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11368, d108079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11369 q = 0) : d108080 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11369, d108080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro390 q selected
    | true =>
      simp only [d11369, d108080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11370 q = 0) : d108081 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11370, d108081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11370, d108081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11371 q = 0) : d108082 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11371, d108082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11371, d108082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11372 q = 0) : d108083 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11372, d108083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11372, d108083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11465 q = 0) : d108151 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11465, d108151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3371 q selected
    | true =>
      simp only [d11465, d108151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11466 q = 0) : d108152 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11466, d108152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11466, d108152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11467 q = 0) : d108153 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11467, d108153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11467, d108153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d11468 q = 0) : d108154 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11468, d108154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d11468, d108154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d11469 q = 0) : d108155 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11469, d108155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11469, d108155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d11470 q = 0) : d108156 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11470, d108156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d11470, d108156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro7575 (p : Pattern) (selected : d11476 p = 0) : d108162 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11471 q = 0) : d108157 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11471, d108157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7574 q selected
    | true =>
      simp only [d11471, d108157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11472 q = 0) : d108158 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11472, d108158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11472, d108158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11473 q = 0) : d108159 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11473, d108159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11473, d108159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11474 q = 0) : d108160 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11474, d108160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11474, d108160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11475 q = 0) : d108161 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11475, d108161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11475, d108161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11476 q = 0) : d108162 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11476, d108162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11476, d108162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7576 (p : Pattern) (selected : d11482 p = 0) : d108168 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11413 q = 0) : d108124 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11413, d108124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7564 q selected
    | true =>
      simp only [d11413, d108124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7565 q selected
  have h2 (q : Pattern) (selected : d11414 q = 0) : d108125 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11414, d108125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11414, d108125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11415 q = 0) : d108126 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11415, d108126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11415, d108126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11416 q = 0) : d108127 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11416, d108127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11416, d108127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11423 q = 0) : d108134 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11423, d108134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7566 q selected
    | true =>
      simp only [d11423, d108134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7567 q selected
  have h6 (q : Pattern) (selected : d11424 q = 0) : d108135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11424, d108135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11424, d108135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11425 q = 0) : d108136 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11425, d108136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11425, d108136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11438 q = 0) : d108149 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11438, d108149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7569 q selected
    | true =>
      simp only [d11438, d108149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7558 q selected
  have h9 (q : Pattern) (selected : d11463 q = 0) : d108101 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11463, d108101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7572 q selected
    | true =>
      simp only [d11463, d108101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7573 q selected
  have h10 (q : Pattern) (selected : d11464 q = 0) : d108150 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11464, d108150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d11464, d108150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d11477 q = 0) : d108163 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11477, d108163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7575 q selected
    | true =>
      simp only [d11477, d108163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d11478 q = 0) : d108164 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11478, d108164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d11478, d108164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d11479 q = 0) : d108165 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11479, d108165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d11479, d108165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d11480 q = 0) : d108166 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11480, d108166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11480, d108166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d11481 q = 0) : d108167 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11481, d108167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11481, d108167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d11482 q = 0) : d108168 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11482, d108168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11482, d108168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro7577 (p : Pattern) (selected : d11483 p = 0) : d108169 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11376 q = 0) : d108087 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d108087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7556 q selected
    | true =>
      simp only [d11376, d108087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11377 q = 0) : d108088 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d108088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11377, d108088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11380 q = 0) : d108091 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d108091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7557 q selected
    | true =>
      simp only [d11380, d108091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11381 q = 0) : d108092 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d108092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11381, d108092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11382 q = 0) : d108093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d108093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11382, d108093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11383 q = 0) : d108094 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11383, d108094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11383, d108094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11409 q = 0) : d108120 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11409, d108120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11409, d108120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11483 q = 0) : d108169 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11483, d108169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11483, d108169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7578 (p : Pattern) (selected : d11484 p = 0) : d108170 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11380 q = 0) : d108091 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d108091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7557 q selected
    | true =>
      simp only [d11380, d108091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11381 q = 0) : d108092 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d108092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11381, d108092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11386 q = 0) : d108097 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11386, d108097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11386, d108097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11387 q = 0) : d108098 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11387, d108098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11387, d108098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11411 q = 0) : d108122 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11411, d108122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11411, d108122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11484 q = 0) : d108170 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11484, d108170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11484, d108170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7579 (p : Pattern) (selected : d11489 p = 0) : d108175 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11376 q = 0) : d108087 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d108087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7556 q selected
    | true =>
      simp only [d11376, d108087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11377 q = 0) : d108088 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d108088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11377, d108088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11380 q = 0) : d108091 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d108091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7557 q selected
    | true =>
      simp only [d11380, d108091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11381 q = 0) : d108092 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d108092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11381, d108092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11382 q = 0) : d108093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11382, d108093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11382, d108093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11417 q = 0) : d108128 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11417, d108128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11417, d108128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11418 q = 0) : d108129 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11418, d108129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11418, d108129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11489 q = 0) : d108175 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11489, d108175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11489, d108175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7580 (p : Pattern) (selected : d11490 p = 0) : d108176 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11380 q = 0) : d108091 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11380, d108091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7557 q selected
    | true =>
      simp only [d11380, d108091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11381 q = 0) : d108092 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11381, d108092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11381, d108092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11386 q = 0) : d108097 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11386, d108097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11386, d108097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11420 q = 0) : d108131 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11420, d108131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11420, d108131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11421 q = 0) : d108132 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11421, d108132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11421, d108132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11490 q = 0) : d108176 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11490, d108176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11490, d108176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7581 (p : Pattern) (selected : d11494 p = 0) : d108180 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11432 q = 0) : d108143 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11432, d108143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7568 q selected
    | true =>
      simp only [d11432, d108143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11433 q = 0) : d108144 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11433, d108144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11433, d108144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11376 q = 0) : d108087 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11376, d108087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7556 q selected
    | true =>
      simp only [d11376, d108087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11377 q = 0) : d108088 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11377, d108088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11377, d108088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11434 q = 0) : d108145 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11434, d108145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11434, d108145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11435 q = 0) : d108146 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11435, d108146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11435, d108146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11436 q = 0) : d108147 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11436, d108147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11436, d108147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11494 q = 0) : d108180 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11494, d108180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11494, d108180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7582 (p : Pattern) (selected : d11496 p = 0) : d108109 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11449 q = 0) : d108087 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11449, d108087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7570 q selected
    | true =>
      simp only [d11449, d108087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11450 q = 0) : d108088 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11450, d108088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11450, d108088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11453 q = 0) : d108091 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11453, d108091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7571 q selected
    | true =>
      simp only [d11453, d108091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11454 q = 0) : d108092 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11454, d108092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11454, d108092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11455 q = 0) : d108093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11455, d108093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11455, d108093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11456 q = 0) : d108094 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11456, d108094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11456, d108094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11457 q = 0) : d108095 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11457, d108095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11457, d108095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11496 q = 0) : d108109 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11496, d108109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11496, d108109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7583 (p : Pattern) (selected : d11497 p = 0) : d108110 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11453 q = 0) : d108091 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11453, d108091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7571 q selected
    | true =>
      simp only [d11453, d108091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11454 q = 0) : d108092 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11454, d108092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11454, d108092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11459 q = 0) : d108097 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11459, d108097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11459, d108097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11460 q = 0) : d108098 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11460, d108098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11460, d108098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11461 q = 0) : d108099 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11461, d108099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11461, d108099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11497 q = 0) : d108110 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11497, d108110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11497, d108110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7584 (p : Pattern) (selected : d11500 p = 0) : d108183 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11471 q = 0) : d108157 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11471, d108157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7574 q selected
    | true =>
      simp only [d11471, d108157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11472 q = 0) : d108158 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11472, d108158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11472, d108158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11473 q = 0) : d108159 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11473, d108159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11473, d108159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11474 q = 0) : d108160 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11474, d108160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11474, d108160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11475 q = 0) : d108161 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11475, d108161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11475, d108161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11500 q = 0) : d108183 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11500, d108183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11500, d108183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7585 (p : Pattern) (selected : d11506 p = 0) : d108189 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11413 q = 0) : d108124 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11413, d108124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7564 q selected
    | true =>
      simp only [d11413, d108124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7565 q selected
  have h2 (q : Pattern) (selected : d11414 q = 0) : d108125 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11414, d108125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11414, d108125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11415 q = 0) : d108126 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11415, d108126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11415, d108126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11416 q = 0) : d108127 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11416, d108127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11416, d108127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11423 q = 0) : d108134 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11423, d108134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7566 q selected
    | true =>
      simp only [d11423, d108134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7567 q selected
  have h6 (q : Pattern) (selected : d11424 q = 0) : d108135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11424, d108135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11424, d108135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11425 q = 0) : d108136 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11425, d108136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11425, d108136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11438 q = 0) : d108149 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11438, d108149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7569 q selected
    | true =>
      simp only [d11438, d108149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7558 q selected
  have h9 (q : Pattern) (selected : d11463 q = 0) : d108101 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11463, d108101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7572 q selected
    | true =>
      simp only [d11463, d108101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7573 q selected
  have h10 (q : Pattern) (selected : d11464 q = 0) : d108150 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11464, d108150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d11464, d108150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d11477 q = 0) : d108163 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11477, d108163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7575 q selected
    | true =>
      simp only [d11477, d108163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d11478 q = 0) : d108164 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11478, d108164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d11478, d108164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d11479 q = 0) : d108165 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11479, d108165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d11479, d108165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d11480 q = 0) : d108166 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11480, d108166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11480, d108166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d11481 q = 0) : d108167 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11481, d108167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11481, d108167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d11485 q = 0) : d108171 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11485, d108171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7577 q selected
    | true =>
      simp only [d11485, d108171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7578 q selected
  have h17 (q : Pattern) (selected : d11486 q = 0) : d108172 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11486, d108172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11486, d108172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d11487 q = 0) : d108173 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11487, d108173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d11487, d108173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d11488 q = 0) : d108174 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11488, d108174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11488, d108174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d11491 q = 0) : d108177 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11491, d108177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7579 q selected
    | true =>
      simp only [d11491, d108177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7580 q selected
  have h21 (q : Pattern) (selected : d11492 q = 0) : d108178 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11492, d108178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11492, d108178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d11493 q = 0) : d108179 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11493, d108179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d11493, d108179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d11495 q = 0) : d108181 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11495, d108181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7581 q selected
    | true =>
      simp only [d11495, d108181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7561 q selected
  have h24 (q : Pattern) (selected : d11498 q = 0) : d108111 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11498, d108111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7582 q selected
    | true =>
      simp only [d11498, d108111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7583 q selected
  have h25 (q : Pattern) (selected : d11499 q = 0) : d108182 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11499, d108182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d11499, d108182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d11501 q = 0) : d108184 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11501, d108184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7584 q selected
    | true =>
      simp only [d11501, d108184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d11502 q = 0) : d108185 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11502, d108185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d11502, d108185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d11503 q = 0) : d108186 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11503, d108186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d11503, d108186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d11504 q = 0) : d108187 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11504, d108187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d11504, d108187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d11505 q = 0) : d108188 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11505, d108188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d11505, d108188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d11506 q = 0) : d108189 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11506, d108189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d11506, d108189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro7586 (p : Pattern) (selected : d11513 p = 0) : d108196 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11390 q = 0) : d108101 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11390, d108101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7558 q selected
    | true =>
      simp only [d11390, d108101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7559 q selected
  have h2 (q : Pattern) (selected : d11391 q = 0) : d108102 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11391, d108102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11391, d108102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11392 q = 0) : d108103 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11392, d108103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11392, d108103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11393 q = 0) : d108104 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11393, d108104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11393, d108104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11394 q = 0) : d108105 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11394, d108105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11394, d108105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11508 q = 0) : d108191 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11508, d108191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7559 q selected
    | true =>
      simp only [d11508, d108191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11509 q = 0) : d108192 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11509, d108192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11509, d108192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11510 q = 0) : d108193 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11510, d108193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11510, d108193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11511 q = 0) : d108194 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11511, d108194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11511, d108194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11512 q = 0) : d108195 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11512, d108195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11512, d108195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d11513 q = 0) : d108196 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11513, d108196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11513, d108196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro7587 (p : Pattern) (selected : d11519 p = 0) : d108202 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11508 q = 0) : d108191 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11508, d108191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7559 q selected
    | true =>
      simp only [d11508, d108191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11509 q = 0) : d108192 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11509, d108192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11509, d108192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11510 q = 0) : d108193 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11510, d108193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11510, d108193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11511 q = 0) : d108194 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11511, d108194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11511, d108194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11512 q = 0) : d108195 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11512, d108195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11512, d108195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11514 q = 0) : d108197 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11514, d108197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7562 q selected
    | true =>
      simp only [d11514, d108197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11515 q = 0) : d108198 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11515, d108198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11515, d108198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11516 q = 0) : d108199 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11516, d108199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11516, d108199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11517 q = 0) : d108200 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11517, d108200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11517, d108200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11518 q = 0) : d108201 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11518, d108201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11518, d108201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d11519 q = 0) : d108202 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11519, d108202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11519, d108202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro7588 (p : Pattern) (selected : d11526 p = 0) : d108209 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11495 q = 0) : d108181 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11495, d108181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7581 q selected
    | true =>
      simp only [d11495, d108181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7561 q selected
  have h2 (q : Pattern) (selected : d11498 q = 0) : d108111 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11498, d108111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7582 q selected
    | true =>
      simp only [d11498, d108111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7583 q selected
  have h3 (q : Pattern) (selected : d11499 q = 0) : d108182 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11499, d108182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d11499, d108182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11501 q = 0) : d108184 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11501, d108184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7584 q selected
    | true =>
      simp only [d11501, d108184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11502 q = 0) : d108185 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11502, d108185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11502, d108185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11503 q = 0) : d108186 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11503, d108186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11503, d108186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11524 q = 0) : d108207 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11524, d108207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11524, d108207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11525 q = 0) : d108208 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11525, d108208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11525, d108208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d11526 q = 0) : d108209 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11526, d108209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11526, d108209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7589 (p : Pattern) (selected : d11528 p = 0) : d108211 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11514 q = 0) : d108197 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11514, d108197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7562 q selected
    | true =>
      simp only [d11514, d108197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11515 q = 0) : d108198 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11515, d108198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11515, d108198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11516 q = 0) : d108199 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11516, d108199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11516, d108199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11517 q = 0) : d108200 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11517, d108200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11517, d108200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11518 q = 0) : d108201 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11518, d108201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11518, d108201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11528 q = 0) : d108211 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11528, d108211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11528, d108211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7590 (p : Pattern) (selected : d11546 p = 0) : d108229 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11534 q = 0) : d108217 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11534, d108217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro439 q selected
    | true =>
      simp only [d11534, d108217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11535 q = 0) : d108218 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11535, d108218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11535, d108218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11536 q = 0) : d108219 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11536, d108219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11536, d108219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11537 q = 0) : d108220 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11537, d108220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro440 q selected
    | true =>
      simp only [d11537, d108220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11538 q = 0) : d108221 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11538, d108221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11538, d108221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11539 q = 0) : d108222 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11539, d108222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11539, d108222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11540 q = 0) : d108223 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11540, d108223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11540, d108223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11541 q = 0) : d108224 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11541, d108224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro441 q selected
    | true =>
      simp only [d11541, d108224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11542 q = 0) : d108225 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11542, d108225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11542, d108225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11543 q = 0) : d108226 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11543, d108226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11543, d108226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d11544 q = 0) : d108227 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11544, d108227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11544, d108227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d11545 q = 0) : d108228 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11545, d108228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11545, d108228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d11546 q = 0) : d108229 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11546, d108229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d11546, d108229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro7591 (p : Pattern) (selected : d11551 p = 0) : d108234 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11537 q = 0) : d108220 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11537, d108220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro440 q selected
    | true =>
      simp only [d11537, d108220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11538 q = 0) : d108221 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11538, d108221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11538, d108221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11539 q = 0) : d108222 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11539, d108222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11539, d108222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11541 q = 0) : d108224 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11541, d108224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro441 q selected
    | true =>
      simp only [d11541, d108224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11542 q = 0) : d108225 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11542, d108225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11542, d108225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11543 q = 0) : d108226 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11543, d108226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11543, d108226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11544 q = 0) : d108227 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11544, d108227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11544, d108227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11549 q = 0) : d108232 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11549, d108232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11549, d108232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11550 q = 0) : d108233 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11550, d108233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11550, d108233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11551 q = 0) : d108234 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11551, d108234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d11551, d108234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro7592 (p : Pattern) (selected : d11557 p = 0) : d108240 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11547 q = 0) : d108230 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11547, d108230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7590 q selected
    | true =>
      simp only [d11547, d108230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11548 q = 0) : d108231 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11548, d108231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11548, d108231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11552 q = 0) : d108235 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11552, d108235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7591 q selected
    | true =>
      simp only [d11552, d108235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11553 q = 0) : d108236 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11553, d108236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11553, d108236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11554 q = 0) : d108237 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11554, d108237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11554, d108237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11555 q = 0) : d108238 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11555, d108238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11555, d108238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11556 q = 0) : d108239 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11556, d108239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11556, d108239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11557 q = 0) : d108240 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11557, d108240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11557, d108240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7593 (p : Pattern) (selected : d11559 p = 0) : d108242 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11541 q = 0) : d108224 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11541, d108224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro441 q selected
    | true =>
      simp only [d11541, d108224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11542 q = 0) : d108225 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11542, d108225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11542, d108225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11543 q = 0) : d108226 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11543, d108226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11543, d108226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11549 q = 0) : d108232 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11549, d108232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11549, d108232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11558 q = 0) : d108241 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11558, d108241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11558, d108241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11559 q = 0) : d108242 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11559, d108242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11559, d108242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7594 (p : Pattern) (selected : d11565 p = 0) : d108248 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11552 q = 0) : d108235 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11552, d108235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7591 q selected
    | true =>
      simp only [d11552, d108235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11553 q = 0) : d108236 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11553, d108236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11553, d108236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11560 q = 0) : d108243 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11560, d108243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7593 q selected
    | true =>
      simp only [d11560, d108243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11561 q = 0) : d108244 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11561, d108244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11561, d108244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11562 q = 0) : d108245 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11562, d108245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11562, d108245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11563 q = 0) : d108246 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11563, d108246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11563, d108246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11564 q = 0) : d108247 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11564, d108247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11564, d108247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11565 q = 0) : d108248 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11565, d108248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11565, d108248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7595 (p : Pattern) (selected : d11576 p = 0) : d108234 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11567 q = 0) : d108220 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11567, d108220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro448 q selected
    | true =>
      simp only [d11567, d108220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11568 q = 0) : d108221 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11568, d108221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11568, d108221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11569 q = 0) : d108222 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11569, d108222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11569, d108222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11570 q = 0) : d108224 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11570, d108224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro449 q selected
    | true =>
      simp only [d11570, d108224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11571 q = 0) : d108225 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11571, d108225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11571, d108225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11572 q = 0) : d108226 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11572, d108226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11572, d108226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11573 q = 0) : d108227 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11573, d108227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11573, d108227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11574 q = 0) : d108232 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11574, d108232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11574, d108232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11575 q = 0) : d108233 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11575, d108233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11575, d108233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11576 q = 0) : d108234 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11576, d108234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d11576, d108234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro7596 (p : Pattern) (selected : d11580 p = 0) : d108242 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11570 q = 0) : d108224 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11570, d108224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro449 q selected
    | true =>
      simp only [d11570, d108224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11571 q = 0) : d108225 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11571, d108225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11571, d108225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11572 q = 0) : d108226 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11572, d108226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11572, d108226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11574 q = 0) : d108232 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11574, d108232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11574, d108232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11579 q = 0) : d108241 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11579, d108241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11579, d108241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11580 q = 0) : d108242 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11580, d108242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11580, d108242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7597 (p : Pattern) (selected : d11586 p = 0) : d108248 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11577 q = 0) : d108235 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11577, d108235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7595 q selected
    | true =>
      simp only [d11577, d108235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11578 q = 0) : d108236 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11578, d108236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11578, d108236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11581 q = 0) : d108243 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11581, d108243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7596 q selected
    | true =>
      simp only [d11581, d108243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11582 q = 0) : d108244 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11582, d108244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11582, d108244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11583 q = 0) : d108245 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11583, d108245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11583, d108245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11584 q = 0) : d108246 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11584, d108246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11584, d108246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11585 q = 0) : d108247 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11585, d108247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11585, d108247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11586 q = 0) : d108248 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11586, d108248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11586, d108248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7598 (p : Pattern) (selected : d11590 p = 0) : d108253 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11581 q = 0) : d108243 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11581, d108243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7596 q selected
    | true =>
      simp only [d11581, d108243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11582 q = 0) : d108244 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11582, d108244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11582, d108244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11587 q = 0) : d108250 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11587, d108250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11587, d108250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11588 q = 0) : d108251 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11588, d108251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11588, d108251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11589 q = 0) : d108252 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11589, d108252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11589, d108252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11590 q = 0) : d108253 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11590, d108253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11590, d108253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7599 (p : Pattern) (selected : d11598 p = 0) : d108261 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11537 q = 0) : d108220 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11537, d108220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro440 q selected
    | true =>
      simp only [d11537, d108220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11538 q = 0) : d108221 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11538, d108221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11538, d108221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11539 q = 0) : d108222 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11539, d108222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11539, d108222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11541 q = 0) : d108224 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11541, d108224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro441 q selected
    | true =>
      simp only [d11541, d108224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11542 q = 0) : d108225 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11542, d108225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11542, d108225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11543 q = 0) : d108226 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11543, d108226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11543, d108226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11544 q = 0) : d108227 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11544, d108227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11544, d108227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11593 q = 0) : d108256 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11593, d108256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3379 q selected
    | true =>
      simp only [d11593, d108256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11594 q = 0) : d108257 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11594, d108257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11594, d108257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11595 q = 0) : d108258 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11595, d108258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11595, d108258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d11596 q = 0) : d108259 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11596, d108259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d11596, d108259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d11597 q = 0) : d108260 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11597, d108260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11597, d108260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d11598 q = 0) : d108261 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11598, d108261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d11598, d108261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro7600 (p : Pattern) (selected : d11604 p = 0) : d108267 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11599 q = 0) : d108262 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11599, d108262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7599 q selected
    | true =>
      simp only [d11599, d108262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11600 q = 0) : d108263 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11600, d108263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11600, d108263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11601 q = 0) : d108264 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11601, d108264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11601, d108264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11602 q = 0) : d108265 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11602, d108265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11602, d108265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11603 q = 0) : d108266 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11603, d108266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11603, d108266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11604 q = 0) : d108267 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11604, d108267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11604, d108267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7601 (p : Pattern) (selected : d11610 p = 0) : d108273 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11566 q = 0) : d108249 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11566, d108249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7592 q selected
    | true =>
      simp only [d11566, d108249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7594 q selected
  have h2 (q : Pattern) (selected : d11591 q = 0) : d108254 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11591, d108254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7597 q selected
    | true =>
      simp only [d11591, d108254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7598 q selected
  have h3 (q : Pattern) (selected : d11592 q = 0) : d108255 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11592, d108255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d11592, d108255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11605 q = 0) : d108268 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11605, d108268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7600 q selected
    | true =>
      simp only [d11605, d108268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11606 q = 0) : d108269 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11606, d108269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11606, d108269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11607 q = 0) : d108270 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11607, d108270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11607, d108270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11608 q = 0) : d108271 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11608, d108271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11608, d108271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11609 q = 0) : d108272 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11609, d108272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11609, d108272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d11610 q = 0) : d108273 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11610, d108273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11610, d108273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7602 (p : Pattern) (selected : d11615 p = 0) : d108253 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11560 q = 0) : d108243 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11560, d108243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7593 q selected
    | true =>
      simp only [d11560, d108243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11561 q = 0) : d108244 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11561, d108244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11561, d108244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11612 q = 0) : d108250 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11612, d108250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11612, d108250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11613 q = 0) : d108251 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11613, d108251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11613, d108251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11614 q = 0) : d108252 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11614, d108252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11614, d108252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11615 q = 0) : d108253 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11615, d108253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11615, d108253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7603 (p : Pattern) (selected : d11621 p = 0) : d108280 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11616 q = 0) : d108275 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11616, d108275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7602 q selected
    | true =>
      simp only [d11616, d108275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11617 q = 0) : d108276 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11617, d108276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11617, d108276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11618 q = 0) : d108277 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11618, d108277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11618, d108277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11619 q = 0) : d108278 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11619, d108278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11619, d108278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11620 q = 0) : d108279 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11620, d108279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11620, d108279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11621 q = 0) : d108280 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11621, d108280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11621, d108280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7604 (p : Pattern) (selected : d11627 p = 0) : d108286 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11396 q = 0) : d108107 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11396, d108107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11396, d108107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7560 q selected
  have h2 (q : Pattern) (selected : d11397 q = 0) : d108108 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11397, d108108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d11397, d108108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d11406 q = 0) : d108117 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11406, d108117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7560 q selected
    | true =>
      simp only [d11406, d108117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7563 q selected
  have h4 (q : Pattern) (selected : d11407 q = 0) : d108118 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11407, d108118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11407, d108118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11408 q = 0) : d108119 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11408, d108119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11408, d108119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11507 q = 0) : d108190 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11507, d108190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7576 q selected
    | true =>
      simp only [d11507, d108190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7585 q selected
  have h7 (q : Pattern) (selected : d11520 q = 0) : d108203 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11520, d108203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7586 q selected
    | true =>
      simp only [d11520, d108203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7587 q selected
  have h8 (q : Pattern) (selected : d11521 q = 0) : d108204 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11521, d108204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11521, d108204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d11522 q = 0) : d108205 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11522, d108205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d11522, d108205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d11523 q = 0) : d108206 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d11523, d108206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11523, d108206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d11527 q = 0) : d108210 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11527, d108210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11527, d108210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7588 q selected
  have h12 (q : Pattern) (selected : d11529 q = 0) : d108212 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11529, d108212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11529, d108212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7589 q selected
  have h13 (q : Pattern) (selected : d11530 q = 0) : d108213 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11530, d108213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d11530, d108213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d11531 q = 0) : d108214 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11531, d108214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d11531, d108214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d11532 q = 0) : d108215 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d11532, d108215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d11532, d108215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d11533 q = 0) : d108216 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d11533, d108216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d11533, d108216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d11611 q = 0) : d108274 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11611, d108274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11611, d108274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7601 q selected
  have h18 (q : Pattern) (selected : d11622 q = 0) : d108281 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11622, d108281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11622, d108281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7603 q selected
  have h19 (q : Pattern) (selected : d11623 q = 0) : d108282 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11623, d108282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d11623, d108282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d11624 q = 0) : d108283 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11624, d108283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d11624, d108283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d11625 q = 0) : d108284 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d11625, d108284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d11625, d108284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d11626 q = 0) : d108285 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d11626, d108285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d11626, d108285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d11627 q = 0) : d108286 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d11627, d108286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d11627, d108286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro7605 (p : Pattern) (selected : d11633 p = 0) : d108292 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11628 q = 0) : d108287 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d11628, d108287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11628, d108287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7604 q selected
  have h2 (q : Pattern) (selected : d11629 q = 0) : d108288 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d11629, d108288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11629, d108288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11630 q = 0) : d108289 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d11630, d108289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11630, d108289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11631 q = 0) : d108290 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d11631, d108290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11631, d108290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11632 q = 0) : d108291 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d11632, d108291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11632, d108291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11633 q = 0) : d108292 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d11633, d108292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11633, d108292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7606 (p : Pattern) (selected : d11646 p = 0) : d108305 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11637 q = 0) : d108296 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11637, d108296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro471 q selected
    | true =>
      simp only [d11637, d108296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11638 q = 0) : d108297 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11638, d108297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11638, d108297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11639 q = 0) : d108298 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11639, d108298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11639, d108298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11640 q = 0) : d108299 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11640, d108299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro472 q selected
    | true =>
      simp only [d11640, d108299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11641 q = 0) : d108300 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11641, d108300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11641, d108300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11642 q = 0) : d108301 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11642, d108301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11642, d108301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11643 q = 0) : d108302 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11643, d108302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11643, d108302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11644 q = 0) : d108303 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11644, d108303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11644, d108303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11645 q = 0) : d108304 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11645, d108304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11645, d108304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11646 q = 0) : d108305 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11646, d108305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d11646, d108305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro7607 (p : Pattern) (selected : d11650 p = 0) : d108309 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11640 q = 0) : d108299 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11640, d108299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro472 q selected
    | true =>
      simp only [d11640, d108299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11641 q = 0) : d108300 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11641, d108300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11641, d108300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11642 q = 0) : d108301 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11642, d108301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11642, d108301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11644 q = 0) : d108303 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11644, d108303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11644, d108303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11649 q = 0) : d108308 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11649, d108308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11649, d108308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11650 q = 0) : d108309 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11650, d108309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11650, d108309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7608 (p : Pattern) (selected : d11656 p = 0) : d108315 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11647 q = 0) : d108306 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d108306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7606 q selected
    | true =>
      simp only [d11647, d108306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11648 q = 0) : d108307 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d108307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11648, d108307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11651 q = 0) : d108310 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d108310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7607 q selected
    | true =>
      simp only [d11651, d108310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11652 q = 0) : d108311 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d108311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11652, d108311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11653 q = 0) : d108312 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d108312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11653, d108312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11654 q = 0) : d108313 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11654, d108313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11654, d108313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11655 q = 0) : d108314 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11655, d108314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11655, d108314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11656 q = 0) : d108315 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11656, d108315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11656, d108315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7609 (p : Pattern) (selected : d11660 p = 0) : d108319 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11651 q = 0) : d108310 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d108310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7607 q selected
    | true =>
      simp only [d11651, d108310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11652 q = 0) : d108311 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d108311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11652, d108311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11657 q = 0) : d108316 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11657, d108316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11657, d108316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11658 q = 0) : d108317 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11658, d108317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11658, d108317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11659 q = 0) : d108318 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11659, d108318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11659, d108318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11660 q = 0) : d108319 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11660, d108319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11660, d108319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7610 (p : Pattern) (selected : d11666 p = 0) : d108325 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11661 q = 0) : d108320 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11661, d108320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7608 q selected
    | true =>
      simp only [d11661, d108320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7609 q selected
  have h2 (q : Pattern) (selected : d11662 q = 0) : d108321 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11662, d108321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11662, d108321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11663 q = 0) : d108322 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11663, d108322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11663, d108322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11664 q = 0) : d108323 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11664, d108323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11664, d108323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11665 q = 0) : d108324 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11665, d108324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11665, d108324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11666 q = 0) : d108325 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11666, d108325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11666, d108325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7611 (p : Pattern) (selected : d11669 p = 0) : d108328 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11647 q = 0) : d108306 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d108306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7606 q selected
    | true =>
      simp only [d11647, d108306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11648 q = 0) : d108307 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d108307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11648, d108307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11651 q = 0) : d108310 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d108310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7607 q selected
    | true =>
      simp only [d11651, d108310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11652 q = 0) : d108311 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d108311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11652, d108311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11653 q = 0) : d108312 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d108312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11653, d108312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11654 q = 0) : d108313 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11654, d108313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11654, d108313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11655 q = 0) : d108314 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11655, d108314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11655, d108314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11669 q = 0) : d108328 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11669, d108328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11669, d108328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7612 (p : Pattern) (selected : d11670 p = 0) : d108329 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11651 q = 0) : d108310 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d108310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7607 q selected
    | true =>
      simp only [d11651, d108310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11652 q = 0) : d108311 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d108311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11652, d108311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11657 q = 0) : d108316 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11657, d108316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11657, d108316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11658 q = 0) : d108317 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11658, d108317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11658, d108317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11659 q = 0) : d108318 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11659, d108318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11659, d108318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11670 q = 0) : d108329 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11670, d108329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11670, d108329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7613 (p : Pattern) (selected : d11676 p = 0) : d108335 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11661 q = 0) : d108320 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11661, d108320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7608 q selected
    | true =>
      simp only [d11661, d108320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7609 q selected
  have h2 (q : Pattern) (selected : d11662 q = 0) : d108321 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11662, d108321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11662, d108321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11663 q = 0) : d108322 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11663, d108322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11663, d108322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11664 q = 0) : d108323 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11664, d108323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11664, d108323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11665 q = 0) : d108324 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11665, d108324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11665, d108324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11671 q = 0) : d108330 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11671, d108330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7611 q selected
    | true =>
      simp only [d11671, d108330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7612 q selected
  have h7 (q : Pattern) (selected : d11672 q = 0) : d108331 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11672, d108331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11672, d108331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11673 q = 0) : d108332 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11673, d108332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11673, d108332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11674 q = 0) : d108333 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11674, d108333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11674, d108333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11675 q = 0) : d108334 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11675, d108334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11675, d108334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d11676 q = 0) : d108335 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11676, d108335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11676, d108335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro7614 (p : Pattern) (selected : d11681 p = 0) : d108340 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11647 q = 0) : d108306 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d108306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7606 q selected
    | true =>
      simp only [d11647, d108306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11648 q = 0) : d108307 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d108307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11648, d108307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11651 q = 0) : d108310 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d108310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7607 q selected
    | true =>
      simp only [d11651, d108310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11652 q = 0) : d108311 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d108311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11652, d108311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11653 q = 0) : d108312 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d108312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11653, d108312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11654 q = 0) : d108313 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11654, d108313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11654, d108313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11680 q = 0) : d108339 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11680, d108339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11680, d108339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11681 q = 0) : d108340 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11681, d108340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11681, d108340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7615 (p : Pattern) (selected : d11683 p = 0) : d108342 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11651 q = 0) : d108310 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d108310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7607 q selected
    | true =>
      simp only [d11651, d108310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11652 q = 0) : d108311 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d108311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11652, d108311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11657 q = 0) : d108316 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11657, d108316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11657, d108316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11658 q = 0) : d108317 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11658, d108317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11658, d108317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11682 q = 0) : d108341 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11682, d108341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11682, d108341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11683 q = 0) : d108342 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11683, d108342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11683, d108342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7616 (p : Pattern) (selected : d11690 p = 0) : d108349 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11647 q = 0) : d108306 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d108306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7606 q selected
    | true =>
      simp only [d11647, d108306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11648 q = 0) : d108307 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d108307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11648, d108307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11651 q = 0) : d108310 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d108310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7607 q selected
    | true =>
      simp only [d11651, d108310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11652 q = 0) : d108311 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d108311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11652, d108311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11653 q = 0) : d108312 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d108312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11653, d108312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11688 q = 0) : d108347 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11688, d108347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11688, d108347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11689 q = 0) : d108348 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11689, d108348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11689, d108348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11690 q = 0) : d108349 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11690, d108349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11690, d108349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7617 (p : Pattern) (selected : d11693 p = 0) : d108352 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11651 q = 0) : d108310 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d108310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7607 q selected
    | true =>
      simp only [d11651, d108310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11652 q = 0) : d108311 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d108311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11652, d108311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11657 q = 0) : d108316 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11657, d108316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11657, d108316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11691 q = 0) : d108350 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11691, d108350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11691, d108350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11692 q = 0) : d108351 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11692, d108351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11692, d108351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11693 q = 0) : d108352 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11693, d108352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11693, d108352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7618 (p : Pattern) (selected : d11702 p = 0) : d108361 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11697 q = 0) : d108356 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11697, d108356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro488 q selected
    | true =>
      simp only [d11697, d108356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11698 q = 0) : d108357 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11698, d108357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11698, d108357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11699 q = 0) : d108358 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11699, d108358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11699, d108358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11637 q = 0) : d108296 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11637, d108296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro471 q selected
    | true =>
      simp only [d11637, d108296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11638 q = 0) : d108297 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11638, d108297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11638, d108297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11639 q = 0) : d108298 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11639, d108298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11639, d108298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11700 q = 0) : d108359 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11700, d108359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11700, d108359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11640 q = 0) : d108299 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11640, d108299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro472 q selected
    | true =>
      simp only [d11640, d108299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11641 q = 0) : d108300 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11641, d108300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11641, d108300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11642 q = 0) : d108301 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11642, d108301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11642, d108301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d11643 q = 0) : d108302 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11643, d108302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11643, d108302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d11701 q = 0) : d108360 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11701, d108360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11701, d108360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d11702 q = 0) : d108361 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11702, d108361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d11702, d108361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro7619 (p : Pattern) (selected : d11708 p = 0) : d108367 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11703 q = 0) : d108362 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11703, d108362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7618 q selected
    | true =>
      simp only [d11703, d108362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11704 q = 0) : d108363 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11704, d108363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11704, d108363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11647 q = 0) : d108306 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d108306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7606 q selected
    | true =>
      simp only [d11647, d108306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11648 q = 0) : d108307 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d108307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11648, d108307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11705 q = 0) : d108364 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11705, d108364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11705, d108364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11706 q = 0) : d108365 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11706, d108365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11706, d108365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11707 q = 0) : d108366 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11707, d108366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11707, d108366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11708 q = 0) : d108367 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11708, d108367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11708, d108367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7620 (p : Pattern) (selected : d11719 p = 0) : d108305 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11710 q = 0) : d108296 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11710, d108296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro504 q selected
    | true =>
      simp only [d11710, d108296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11711 q = 0) : d108297 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11711, d108297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11711, d108297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11712 q = 0) : d108298 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11712, d108298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11712, d108298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11713 q = 0) : d108299 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11713, d108299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro505 q selected
    | true =>
      simp only [d11713, d108299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11714 q = 0) : d108300 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11714, d108300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11714, d108300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11715 q = 0) : d108301 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11715, d108301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11715, d108301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11716 q = 0) : d108302 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11716, d108302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11716, d108302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11717 q = 0) : d108303 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11717, d108303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11717, d108303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11718 q = 0) : d108304 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11718, d108304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11718, d108304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11719 q = 0) : d108305 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11719, d108305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d11719, d108305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro7621 (p : Pattern) (selected : d11723 p = 0) : d108309 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11713 q = 0) : d108299 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11713, d108299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro505 q selected
    | true =>
      simp only [d11713, d108299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11714 q = 0) : d108300 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11714, d108300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11714, d108300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11715 q = 0) : d108301 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11715, d108301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11715, d108301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11717 q = 0) : d108303 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11717, d108303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11717, d108303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11722 q = 0) : d108308 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11722, d108308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11722, d108308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11723 q = 0) : d108309 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11723, d108309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11723, d108309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7622 (p : Pattern) (selected : d11729 p = 0) : d108315 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11720 q = 0) : d108306 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11720, d108306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7620 q selected
    | true =>
      simp only [d11720, d108306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11721 q = 0) : d108307 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11721, d108307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11721, d108307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11724 q = 0) : d108310 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11724, d108310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7621 q selected
    | true =>
      simp only [d11724, d108310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11725 q = 0) : d108311 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11725, d108311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11725, d108311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11726 q = 0) : d108312 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11726, d108312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11726, d108312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11727 q = 0) : d108313 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11727, d108313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11727, d108313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11728 q = 0) : d108314 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11728, d108314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11728, d108314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11729 q = 0) : d108315 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11729, d108315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11729, d108315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7623 (p : Pattern) (selected : d11733 p = 0) : d108319 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11724 q = 0) : d108310 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11724, d108310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7621 q selected
    | true =>
      simp only [d11724, d108310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11725 q = 0) : d108311 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11725, d108311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11725, d108311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11730 q = 0) : d108316 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11730, d108316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11730, d108316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11731 q = 0) : d108317 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11731, d108317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11731, d108317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11732 q = 0) : d108318 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11732, d108318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11732, d108318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11733 q = 0) : d108319 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11733, d108319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11733, d108319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7624 (p : Pattern) (selected : d11741 p = 0) : d108375 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11637 q = 0) : d108296 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11637, d108296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro471 q selected
    | true =>
      simp only [d11637, d108296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11638 q = 0) : d108297 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11638, d108297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11638, d108297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11639 q = 0) : d108298 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11639, d108298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11639, d108298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11640 q = 0) : d108299 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11640, d108299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro472 q selected
    | true =>
      simp only [d11640, d108299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11641 q = 0) : d108300 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11641, d108300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11641, d108300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11642 q = 0) : d108301 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11642, d108301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11642, d108301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11643 q = 0) : d108302 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11643, d108302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11643, d108302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11736 q = 0) : d108370 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11736, d108370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3387 q selected
    | true =>
      simp only [d11736, d108370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11737 q = 0) : d108371 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11737, d108371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11737, d108371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11738 q = 0) : d108372 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11738, d108372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11738, d108372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d11739 q = 0) : d108373 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11739, d108373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d11739, d108373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d11740 q = 0) : d108374 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11740, d108374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11740, d108374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d11741 q = 0) : d108375 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11741, d108375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d11741, d108375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro7625 (p : Pattern) (selected : d11747 p = 0) : d108381 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11742 q = 0) : d108376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11742, d108376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7624 q selected
    | true =>
      simp only [d11742, d108376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11743 q = 0) : d108377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11743, d108377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11743, d108377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11744 q = 0) : d108378 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11744, d108378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11744, d108378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11745 q = 0) : d108379 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11745, d108379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11745, d108379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11746 q = 0) : d108380 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11746, d108380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11746, d108380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11747 q = 0) : d108381 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11747, d108381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11747, d108381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7626 (p : Pattern) (selected : d11753 p = 0) : d108387 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11684 q = 0) : d108343 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11684, d108343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7614 q selected
    | true =>
      simp only [d11684, d108343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7615 q selected
  have h2 (q : Pattern) (selected : d11685 q = 0) : d108344 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11685, d108344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11685, d108344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11686 q = 0) : d108345 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11686, d108345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11686, d108345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11687 q = 0) : d108346 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11687, d108346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11687, d108346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11694 q = 0) : d108353 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11694, d108353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7616 q selected
    | true =>
      simp only [d11694, d108353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7617 q selected
  have h6 (q : Pattern) (selected : d11695 q = 0) : d108354 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11695, d108354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11695, d108354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11696 q = 0) : d108355 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11696, d108355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11696, d108355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11709 q = 0) : d108368 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11709, d108368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7619 q selected
    | true =>
      simp only [d11709, d108368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7608 q selected
  have h9 (q : Pattern) (selected : d11734 q = 0) : d108320 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11734, d108320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7622 q selected
    | true =>
      simp only [d11734, d108320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7623 q selected
  have h10 (q : Pattern) (selected : d11735 q = 0) : d108369 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11735, d108369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d11735, d108369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d11748 q = 0) : d108382 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11748, d108382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7625 q selected
    | true =>
      simp only [d11748, d108382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d11749 q = 0) : d108383 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11749, d108383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d11749, d108383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d11750 q = 0) : d108384 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11750, d108384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d11750, d108384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d11751 q = 0) : d108385 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11751, d108385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11751, d108385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d11752 q = 0) : d108386 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11752, d108386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11752, d108386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d11753 q = 0) : d108387 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11753, d108387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11753, d108387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro7627 (p : Pattern) (selected : d11754 p = 0) : d108388 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11647 q = 0) : d108306 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d108306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7606 q selected
    | true =>
      simp only [d11647, d108306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11648 q = 0) : d108307 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d108307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11648, d108307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11651 q = 0) : d108310 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d108310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7607 q selected
    | true =>
      simp only [d11651, d108310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11652 q = 0) : d108311 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d108311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11652, d108311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11653 q = 0) : d108312 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d108312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11653, d108312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11654 q = 0) : d108313 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11654, d108313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11654, d108313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11680 q = 0) : d108339 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11680, d108339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11680, d108339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11754 q = 0) : d108388 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11754, d108388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11754, d108388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7628 (p : Pattern) (selected : d11755 p = 0) : d108389 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11651 q = 0) : d108310 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d108310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7607 q selected
    | true =>
      simp only [d11651, d108310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11652 q = 0) : d108311 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d108311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11652, d108311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11657 q = 0) : d108316 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11657, d108316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11657, d108316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11658 q = 0) : d108317 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11658, d108317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11658, d108317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11682 q = 0) : d108341 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11682, d108341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11682, d108341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11755 q = 0) : d108389 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11755, d108389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11755, d108389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7629 (p : Pattern) (selected : d11760 p = 0) : d108394 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11647 q = 0) : d108306 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d108306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7606 q selected
    | true =>
      simp only [d11647, d108306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11648 q = 0) : d108307 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d108307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11648, d108307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11651 q = 0) : d108310 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d108310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7607 q selected
    | true =>
      simp only [d11651, d108310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11652 q = 0) : d108311 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d108311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11652, d108311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11653 q = 0) : d108312 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11653, d108312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11653, d108312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11688 q = 0) : d108347 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11688, d108347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11688, d108347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11689 q = 0) : d108348 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11689, d108348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11689, d108348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11760 q = 0) : d108394 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11760, d108394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11760, d108394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7630 (p : Pattern) (selected : d11761 p = 0) : d108395 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11651 q = 0) : d108310 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11651, d108310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7607 q selected
    | true =>
      simp only [d11651, d108310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11652 q = 0) : d108311 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11652, d108311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11652, d108311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11657 q = 0) : d108316 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11657, d108316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11657, d108316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11691 q = 0) : d108350 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11691, d108350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11691, d108350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11692 q = 0) : d108351 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11692, d108351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11692, d108351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11761 q = 0) : d108395 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11761, d108395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11761, d108395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7631 (p : Pattern) (selected : d11765 p = 0) : d108399 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11703 q = 0) : d108362 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11703, d108362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7618 q selected
    | true =>
      simp only [d11703, d108362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11704 q = 0) : d108363 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11704, d108363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11704, d108363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11647 q = 0) : d108306 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11647, d108306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7606 q selected
    | true =>
      simp only [d11647, d108306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11648 q = 0) : d108307 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11648, d108307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11648, d108307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11705 q = 0) : d108364 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11705, d108364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11705, d108364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11706 q = 0) : d108365 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11706, d108365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11706, d108365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11707 q = 0) : d108366 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11707, d108366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11707, d108366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11765 q = 0) : d108399 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11765, d108399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11765, d108399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7632 (p : Pattern) (selected : d11767 p = 0) : d108328 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11720 q = 0) : d108306 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11720, d108306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7620 q selected
    | true =>
      simp only [d11720, d108306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11721 q = 0) : d108307 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11721, d108307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11721, d108307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11724 q = 0) : d108310 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11724, d108310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7621 q selected
    | true =>
      simp only [d11724, d108310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11725 q = 0) : d108311 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11725, d108311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11725, d108311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11726 q = 0) : d108312 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11726, d108312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11726, d108312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11727 q = 0) : d108313 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11727, d108313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11727, d108313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11728 q = 0) : d108314 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11728, d108314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11728, d108314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11767 q = 0) : d108328 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11767, d108328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11767, d108328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7633 (p : Pattern) (selected : d11768 p = 0) : d108329 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11724 q = 0) : d108310 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11724, d108310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7621 q selected
    | true =>
      simp only [d11724, d108310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11725 q = 0) : d108311 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11725, d108311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11725, d108311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11730 q = 0) : d108316 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11730, d108316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11730, d108316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11731 q = 0) : d108317 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11731, d108317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11731, d108317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11732 q = 0) : d108318 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11732, d108318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11732, d108318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11768 q = 0) : d108329 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11768, d108329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11768, d108329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7634 (p : Pattern) (selected : d11771 p = 0) : d108402 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11742 q = 0) : d108376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11742, d108376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7624 q selected
    | true =>
      simp only [d11742, d108376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11743 q = 0) : d108377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11743, d108377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11743, d108377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11744 q = 0) : d108378 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11744, d108378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11744, d108378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11745 q = 0) : d108379 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11745, d108379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11745, d108379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11746 q = 0) : d108380 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11746, d108380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11746, d108380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11771 q = 0) : d108402 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11771, d108402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11771, d108402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7635 (p : Pattern) (selected : d11777 p = 0) : d108408 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11684 q = 0) : d108343 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11684, d108343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7614 q selected
    | true =>
      simp only [d11684, d108343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7615 q selected
  have h2 (q : Pattern) (selected : d11685 q = 0) : d108344 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11685, d108344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11685, d108344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11686 q = 0) : d108345 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11686, d108345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11686, d108345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11687 q = 0) : d108346 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11687, d108346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11687, d108346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11694 q = 0) : d108353 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11694, d108353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7616 q selected
    | true =>
      simp only [d11694, d108353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7617 q selected
  have h6 (q : Pattern) (selected : d11695 q = 0) : d108354 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11695, d108354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11695, d108354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11696 q = 0) : d108355 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11696, d108355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11696, d108355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11709 q = 0) : d108368 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11709, d108368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7619 q selected
    | true =>
      simp only [d11709, d108368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7608 q selected
  have h9 (q : Pattern) (selected : d11734 q = 0) : d108320 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11734, d108320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7622 q selected
    | true =>
      simp only [d11734, d108320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7623 q selected
  have h10 (q : Pattern) (selected : d11735 q = 0) : d108369 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11735, d108369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d11735, d108369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d11748 q = 0) : d108382 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11748, d108382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7625 q selected
    | true =>
      simp only [d11748, d108382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d11749 q = 0) : d108383 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11749, d108383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d11749, d108383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d11750 q = 0) : d108384 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11750, d108384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d11750, d108384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d11751 q = 0) : d108385 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11751, d108385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11751, d108385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d11752 q = 0) : d108386 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11752, d108386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11752, d108386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d11756 q = 0) : d108390 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11756, d108390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7627 q selected
    | true =>
      simp only [d11756, d108390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7628 q selected
  have h17 (q : Pattern) (selected : d11757 q = 0) : d108391 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11757, d108391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11757, d108391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d11758 q = 0) : d108392 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11758, d108392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d11758, d108392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d11759 q = 0) : d108393 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11759, d108393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11759, d108393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d11762 q = 0) : d108396 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11762, d108396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7629 q selected
    | true =>
      simp only [d11762, d108396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7630 q selected
  have h21 (q : Pattern) (selected : d11763 q = 0) : d108397 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11763, d108397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11763, d108397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d11764 q = 0) : d108398 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11764, d108398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d11764, d108398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d11766 q = 0) : d108400 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11766, d108400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7631 q selected
    | true =>
      simp only [d11766, d108400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7611 q selected
  have h24 (q : Pattern) (selected : d11769 q = 0) : d108330 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11769, d108330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7632 q selected
    | true =>
      simp only [d11769, d108330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7633 q selected
  have h25 (q : Pattern) (selected : d11770 q = 0) : d108401 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11770, d108401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d11770, d108401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d11772 q = 0) : d108403 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11772, d108403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7634 q selected
    | true =>
      simp only [d11772, d108403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d11773 q = 0) : d108404 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11773, d108404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d11773, d108404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d11774 q = 0) : d108405 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11774, d108405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d11774, d108405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d11775 q = 0) : d108406 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11775, d108406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d11775, d108406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d11776 q = 0) : d108407 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11776, d108407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d11776, d108407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d11777 q = 0) : d108408 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11777, d108408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d11777, d108408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro7636 (p : Pattern) (selected : d11784 p = 0) : d108415 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11661 q = 0) : d108320 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11661, d108320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7608 q selected
    | true =>
      simp only [d11661, d108320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7609 q selected
  have h2 (q : Pattern) (selected : d11662 q = 0) : d108321 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11662, d108321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11662, d108321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11663 q = 0) : d108322 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11663, d108322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11663, d108322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11664 q = 0) : d108323 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11664, d108323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11664, d108323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11665 q = 0) : d108324 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11665, d108324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11665, d108324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11779 q = 0) : d108410 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11779, d108410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7609 q selected
    | true =>
      simp only [d11779, d108410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11780 q = 0) : d108411 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11780, d108411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11780, d108411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11781 q = 0) : d108412 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11781, d108412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11781, d108412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11782 q = 0) : d108413 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11782, d108413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11782, d108413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11783 q = 0) : d108414 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11783, d108414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11783, d108414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d11784 q = 0) : d108415 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11784, d108415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11784, d108415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro7637 (p : Pattern) (selected : d11790 p = 0) : d108421 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11779 q = 0) : d108410 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11779, d108410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7609 q selected
    | true =>
      simp only [d11779, d108410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11780 q = 0) : d108411 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11780, d108411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11780, d108411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11781 q = 0) : d108412 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11781, d108412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11781, d108412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11782 q = 0) : d108413 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11782, d108413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11782, d108413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11783 q = 0) : d108414 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11783, d108414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11783, d108414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11785 q = 0) : d108416 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11785, d108416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7612 q selected
    | true =>
      simp only [d11785, d108416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11786 q = 0) : d108417 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11786, d108417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11786, d108417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11787 q = 0) : d108418 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11787, d108418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11787, d108418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11788 q = 0) : d108419 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11788, d108419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11788, d108419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11789 q = 0) : d108420 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11789, d108420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11789, d108420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d11790 q = 0) : d108421 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11790, d108421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11790, d108421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro7638 (p : Pattern) (selected : d11797 p = 0) : d108428 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11766 q = 0) : d108400 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11766, d108400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7631 q selected
    | true =>
      simp only [d11766, d108400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7611 q selected
  have h2 (q : Pattern) (selected : d11769 q = 0) : d108330 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11769, d108330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7632 q selected
    | true =>
      simp only [d11769, d108330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7633 q selected
  have h3 (q : Pattern) (selected : d11770 q = 0) : d108401 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11770, d108401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d11770, d108401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11772 q = 0) : d108403 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11772, d108403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7634 q selected
    | true =>
      simp only [d11772, d108403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11773 q = 0) : d108404 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11773, d108404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11773, d108404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11774 q = 0) : d108405 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11774, d108405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11774, d108405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11795 q = 0) : d108426 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11795, d108426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11795, d108426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11796 q = 0) : d108427 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11796, d108427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11796, d108427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d11797 q = 0) : d108428 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11797, d108428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11797, d108428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7639 (p : Pattern) (selected : d11799 p = 0) : d108430 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11785 q = 0) : d108416 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11785, d108416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7612 q selected
    | true =>
      simp only [d11785, d108416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11786 q = 0) : d108417 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11786, d108417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11786, d108417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11787 q = 0) : d108418 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11787, d108418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11787, d108418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11788 q = 0) : d108419 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11788, d108419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11788, d108419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11789 q = 0) : d108420 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11789, d108420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11789, d108420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11799 q = 0) : d108430 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11799, d108430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11799, d108430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7640 (p : Pattern) (selected : d11817 p = 0) : d108448 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11805 q = 0) : d108436 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11805, d108436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro525 q selected
    | true =>
      simp only [d11805, d108436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11806 q = 0) : d108437 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11806, d108437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11806, d108437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11807 q = 0) : d108438 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11807, d108438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11807, d108438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11808 q = 0) : d108439 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11808, d108439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro526 q selected
    | true =>
      simp only [d11808, d108439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11809 q = 0) : d108440 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11809, d108440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11809, d108440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11810 q = 0) : d108441 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11810, d108441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11810, d108441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11811 q = 0) : d108442 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11811, d108442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11811, d108442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11812 q = 0) : d108443 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11812, d108443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro527 q selected
    | true =>
      simp only [d11812, d108443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11813 q = 0) : d108444 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11813, d108444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11813, d108444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11814 q = 0) : d108445 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11814, d108445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11814, d108445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d11815 q = 0) : d108446 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11815, d108446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11815, d108446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d11816 q = 0) : d108447 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11816, d108447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11816, d108447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d11817 q = 0) : d108448 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11817, d108448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d11817, d108448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro7641 (p : Pattern) (selected : d11822 p = 0) : d108453 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11808 q = 0) : d108439 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11808, d108439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro526 q selected
    | true =>
      simp only [d11808, d108439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11809 q = 0) : d108440 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11809, d108440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11809, d108440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11810 q = 0) : d108441 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11810, d108441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11810, d108441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11812 q = 0) : d108443 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11812, d108443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro527 q selected
    | true =>
      simp only [d11812, d108443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11813 q = 0) : d108444 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11813, d108444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11813, d108444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11814 q = 0) : d108445 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11814, d108445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11814, d108445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11815 q = 0) : d108446 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11815, d108446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11815, d108446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11820 q = 0) : d108451 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11820, d108451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11820, d108451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11821 q = 0) : d108452 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11821, d108452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11821, d108452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11822 q = 0) : d108453 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11822, d108453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d11822, d108453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro7642 (p : Pattern) (selected : d11828 p = 0) : d108459 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11818 q = 0) : d108449 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11818, d108449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7640 q selected
    | true =>
      simp only [d11818, d108449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11819 q = 0) : d108450 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11819, d108450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11819, d108450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11823 q = 0) : d108454 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11823, d108454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7641 q selected
    | true =>
      simp only [d11823, d108454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11824 q = 0) : d108455 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11824, d108455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11824, d108455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11825 q = 0) : d108456 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11825, d108456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11825, d108456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11826 q = 0) : d108457 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11826, d108457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11826, d108457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11827 q = 0) : d108458 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11827, d108458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11827, d108458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11828 q = 0) : d108459 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11828, d108459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11828, d108459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7643 (p : Pattern) (selected : d11830 p = 0) : d108461 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11812 q = 0) : d108443 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11812, d108443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro527 q selected
    | true =>
      simp only [d11812, d108443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11813 q = 0) : d108444 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11813, d108444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11813, d108444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11814 q = 0) : d108445 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11814, d108445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11814, d108445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11820 q = 0) : d108451 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11820, d108451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11820, d108451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11829 q = 0) : d108460 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11829, d108460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11829, d108460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11830 q = 0) : d108461 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11830, d108461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11830, d108461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7644 (p : Pattern) (selected : d11836 p = 0) : d108467 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11823 q = 0) : d108454 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11823, d108454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7641 q selected
    | true =>
      simp only [d11823, d108454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11824 q = 0) : d108455 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11824, d108455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11824, d108455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11831 q = 0) : d108462 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11831, d108462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7643 q selected
    | true =>
      simp only [d11831, d108462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11832 q = 0) : d108463 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11832, d108463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11832, d108463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11833 q = 0) : d108464 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11833, d108464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11833, d108464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11834 q = 0) : d108465 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11834, d108465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11834, d108465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11835 q = 0) : d108466 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11835, d108466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11835, d108466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11836 q = 0) : d108467 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11836, d108467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11836, d108467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7645 (p : Pattern) (selected : d11847 p = 0) : d108453 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11838 q = 0) : d108439 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11838, d108439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro534 q selected
    | true =>
      simp only [d11838, d108439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11839 q = 0) : d108440 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11839, d108440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11839, d108440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11840 q = 0) : d108441 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11840, d108441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11840, d108441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11841 q = 0) : d108443 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11841, d108443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro535 q selected
    | true =>
      simp only [d11841, d108443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11842 q = 0) : d108444 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11842, d108444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11842, d108444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11843 q = 0) : d108445 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11843, d108445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11843, d108445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11844 q = 0) : d108446 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11844, d108446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11844, d108446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11845 q = 0) : d108451 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11845, d108451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11845, d108451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11846 q = 0) : d108452 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11846, d108452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11846, d108452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11847 q = 0) : d108453 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11847, d108453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d11847, d108453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro7646 (p : Pattern) (selected : d11851 p = 0) : d108461 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11841 q = 0) : d108443 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11841, d108443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro535 q selected
    | true =>
      simp only [d11841, d108443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11842 q = 0) : d108444 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11842, d108444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11842, d108444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11843 q = 0) : d108445 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11843, d108445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11843, d108445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11845 q = 0) : d108451 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11845, d108451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11845, d108451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11850 q = 0) : d108460 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11850, d108460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11850, d108460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11851 q = 0) : d108461 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11851, d108461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11851, d108461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7647 (p : Pattern) (selected : d11857 p = 0) : d108467 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11848 q = 0) : d108454 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11848, d108454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7645 q selected
    | true =>
      simp only [d11848, d108454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11849 q = 0) : d108455 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11849, d108455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11849, d108455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11852 q = 0) : d108462 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11852, d108462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7646 q selected
    | true =>
      simp only [d11852, d108462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11853 q = 0) : d108463 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11853, d108463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11853, d108463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11854 q = 0) : d108464 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11854, d108464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11854, d108464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11855 q = 0) : d108465 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11855, d108465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11855, d108465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11856 q = 0) : d108466 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11856, d108466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11856, d108466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11857 q = 0) : d108467 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11857, d108467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11857, d108467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7648 (p : Pattern) (selected : d11861 p = 0) : d108472 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11852 q = 0) : d108462 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11852, d108462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7646 q selected
    | true =>
      simp only [d11852, d108462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11853 q = 0) : d108463 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11853, d108463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11853, d108463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11858 q = 0) : d108469 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11858, d108469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11858, d108469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11859 q = 0) : d108470 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11859, d108470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11859, d108470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11860 q = 0) : d108471 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11860, d108471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11860, d108471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11861 q = 0) : d108472 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11861, d108472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11861, d108472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7649 (p : Pattern) (selected : d11869 p = 0) : d108480 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11808 q = 0) : d108439 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11808, d108439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro526 q selected
    | true =>
      simp only [d11808, d108439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11809 q = 0) : d108440 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11809, d108440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11809, d108440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11810 q = 0) : d108441 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11810, d108441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11810, d108441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11812 q = 0) : d108443 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11812, d108443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro527 q selected
    | true =>
      simp only [d11812, d108443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11813 q = 0) : d108444 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11813, d108444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11813, d108444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11814 q = 0) : d108445 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11814, d108445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11814, d108445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11815 q = 0) : d108446 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11815, d108446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11815, d108446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11864 q = 0) : d108475 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11864, d108475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3395 q selected
    | true =>
      simp only [d11864, d108475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11865 q = 0) : d108476 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11865, d108476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11865, d108476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11866 q = 0) : d108477 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11866, d108477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11866, d108477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d11867 q = 0) : d108478 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11867, d108478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d11867, d108478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d11868 q = 0) : d108479 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11868, d108479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11868, d108479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d11869 q = 0) : d108480 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11869, d108480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d11869, d108480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro7650 (p : Pattern) (selected : d11875 p = 0) : d108486 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11870 q = 0) : d108481 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11870, d108481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7649 q selected
    | true =>
      simp only [d11870, d108481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11871 q = 0) : d108482 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11871, d108482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11871, d108482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11872 q = 0) : d108483 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11872, d108483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11872, d108483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11873 q = 0) : d108484 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11873, d108484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11873, d108484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11874 q = 0) : d108485 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11874, d108485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11874, d108485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11875 q = 0) : d108486 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11875, d108486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11875, d108486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7651 (p : Pattern) (selected : d11881 p = 0) : d108492 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11837 q = 0) : d108468 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11837, d108468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7642 q selected
    | true =>
      simp only [d11837, d108468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7644 q selected
  have h2 (q : Pattern) (selected : d11862 q = 0) : d108473 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11862, d108473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7647 q selected
    | true =>
      simp only [d11862, d108473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7648 q selected
  have h3 (q : Pattern) (selected : d11863 q = 0) : d108474 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11863, d108474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d11863, d108474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11876 q = 0) : d108487 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11876, d108487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7650 q selected
    | true =>
      simp only [d11876, d108487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11877 q = 0) : d108488 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11877, d108488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11877, d108488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11878 q = 0) : d108489 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11878, d108489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11878, d108489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11879 q = 0) : d108490 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11879, d108490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11879, d108490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11880 q = 0) : d108491 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11880, d108491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11880, d108491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d11881 q = 0) : d108492 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11881, d108492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11881, d108492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7652 (p : Pattern) (selected : d11886 p = 0) : d108472 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11831 q = 0) : d108462 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11831, d108462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7643 q selected
    | true =>
      simp only [d11831, d108462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11832 q = 0) : d108463 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11832, d108463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11832, d108463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11883 q = 0) : d108469 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11883, d108469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11883, d108469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11884 q = 0) : d108470 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11884, d108470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11884, d108470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11885 q = 0) : d108471 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11885, d108471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11885, d108471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11886 q = 0) : d108472 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11886, d108472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11886, d108472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7653 (p : Pattern) (selected : d11892 p = 0) : d108499 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11887 q = 0) : d108494 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11887, d108494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7652 q selected
    | true =>
      simp only [d11887, d108494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11888 q = 0) : d108495 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11888, d108495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11888, d108495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11889 q = 0) : d108496 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11889, d108496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11889, d108496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11890 q = 0) : d108497 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11890, d108497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11890, d108497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11891 q = 0) : d108498 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11891, d108498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11891, d108498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11892 q = 0) : d108499 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11892, d108499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11892, d108499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7654 (p : Pattern) (selected : d11898 p = 0) : d108505 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11667 q = 0) : d108326 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11667, d108326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11667, d108326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7610 q selected
  have h2 (q : Pattern) (selected : d11668 q = 0) : d108327 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11668, d108327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d11668, d108327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d11677 q = 0) : d108336 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11677, d108336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7610 q selected
    | true =>
      simp only [d11677, d108336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7613 q selected
  have h4 (q : Pattern) (selected : d11678 q = 0) : d108337 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11678, d108337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11678, d108337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11679 q = 0) : d108338 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11679, d108338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11679, d108338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11778 q = 0) : d108409 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11778, d108409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7626 q selected
    | true =>
      simp only [d11778, d108409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7635 q selected
  have h7 (q : Pattern) (selected : d11791 q = 0) : d108422 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11791, d108422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7636 q selected
    | true =>
      simp only [d11791, d108422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7637 q selected
  have h8 (q : Pattern) (selected : d11792 q = 0) : d108423 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11792, d108423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11792, d108423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d11793 q = 0) : d108424 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11793, d108424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d11793, d108424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d11794 q = 0) : d108425 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d11794, d108425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11794, d108425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d11798 q = 0) : d108429 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11798, d108429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11798, d108429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7638 q selected
  have h12 (q : Pattern) (selected : d11800 q = 0) : d108431 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11800, d108431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11800, d108431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7639 q selected
  have h13 (q : Pattern) (selected : d11801 q = 0) : d108432 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11801, d108432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d11801, d108432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d11802 q = 0) : d108433 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11802, d108433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d11802, d108433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d11803 q = 0) : d108434 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d11803, d108434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d11803, d108434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d11804 q = 0) : d108435 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d11804, d108435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d11804, d108435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d11882 q = 0) : d108493 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11882, d108493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11882, d108493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7651 q selected
  have h18 (q : Pattern) (selected : d11893 q = 0) : d108500 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11893, d108500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11893, d108500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7653 q selected
  have h19 (q : Pattern) (selected : d11894 q = 0) : d108501 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11894, d108501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d11894, d108501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d11895 q = 0) : d108502 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11895, d108502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d11895, d108502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d11896 q = 0) : d108503 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d11896, d108503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d11896, d108503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d11897 q = 0) : d108504 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d11897, d108504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d11897, d108504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d11898 q = 0) : d108505 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d11898, d108505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d11898, d108505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro7655 (p : Pattern) (selected : d11904 p = 0) : d108511 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11899 q = 0) : d108506 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d11899, d108506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11899, d108506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7654 q selected
  have h2 (q : Pattern) (selected : d11900 q = 0) : d108507 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d11900, d108507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11900, d108507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11901 q = 0) : d108508 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d11901, d108508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11901, d108508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11902 q = 0) : d108509 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d11902, d108509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11902, d108509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11903 q = 0) : d108510 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d11903, d108510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11903, d108510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11904 q = 0) : d108511 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d11904, d108511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11904, d108511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7656 (p : Pattern) (selected : d11918 p = 0) : d108525 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11909 q = 0) : d108516 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11909, d108516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro560 q selected
    | true =>
      simp only [d11909, d108516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11910 q = 0) : d108517 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11910, d108517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11910, d108517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11911 q = 0) : d108518 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11911, d108518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11911, d108518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11912 q = 0) : d108519 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11912, d108519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro561 q selected
    | true =>
      simp only [d11912, d108519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11913 q = 0) : d108520 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11913, d108520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11913, d108520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11914 q = 0) : d108521 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11914, d108521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11914, d108521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11915 q = 0) : d108522 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11915, d108522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11915, d108522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11916 q = 0) : d108523 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11916, d108523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11916, d108523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11917 q = 0) : d108524 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11917, d108524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11917, d108524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11918 q = 0) : d108525 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11918, d108525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d11918, d108525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro7657 (p : Pattern) (selected : d11922 p = 0) : d108529 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11912 q = 0) : d108519 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11912, d108519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro561 q selected
    | true =>
      simp only [d11912, d108519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11913 q = 0) : d108520 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11913, d108520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11913, d108520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11914 q = 0) : d108521 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11914, d108521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11914, d108521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11916 q = 0) : d108523 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11916, d108523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11916, d108523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11921 q = 0) : d108528 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11921, d108528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11921, d108528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11922 q = 0) : d108529 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11922, d108529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11922, d108529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7658 (p : Pattern) (selected : d11928 p = 0) : d108535 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11919 q = 0) : d108526 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d108526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7656 q selected
    | true =>
      simp only [d11919, d108526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11920 q = 0) : d108527 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d108527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11920, d108527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11923 q = 0) : d108530 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d108530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7657 q selected
    | true =>
      simp only [d11923, d108530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11924 q = 0) : d108531 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d108531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11924, d108531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11925 q = 0) : d108532 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d108532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11925, d108532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11926 q = 0) : d108533 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11926, d108533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11926, d108533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11927 q = 0) : d108534 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11927, d108534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11927, d108534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11928 q = 0) : d108535 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11928, d108535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11928, d108535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7659 (p : Pattern) (selected : d11932 p = 0) : d108539 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11923 q = 0) : d108530 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d108530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7657 q selected
    | true =>
      simp only [d11923, d108530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11924 q = 0) : d108531 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d108531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11924, d108531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11929 q = 0) : d108536 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11929, d108536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11929, d108536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11930 q = 0) : d108537 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11930, d108537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11930, d108537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11931 q = 0) : d108538 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11931, d108538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11931, d108538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11932 q = 0) : d108539 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11932, d108539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11932, d108539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7660 (p : Pattern) (selected : d11938 p = 0) : d108545 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11933 q = 0) : d108540 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11933, d108540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7658 q selected
    | true =>
      simp only [d11933, d108540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7659 q selected
  have h2 (q : Pattern) (selected : d11934 q = 0) : d108541 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11934, d108541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11934, d108541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11935 q = 0) : d108542 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11935, d108542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11935, d108542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11936 q = 0) : d108543 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11936, d108543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11936, d108543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11937 q = 0) : d108544 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11937, d108544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11937, d108544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11938 q = 0) : d108545 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11938, d108545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11938, d108545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7661 (p : Pattern) (selected : d11941 p = 0) : d108548 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11919 q = 0) : d108526 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d108526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7656 q selected
    | true =>
      simp only [d11919, d108526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11920 q = 0) : d108527 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d108527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11920, d108527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11923 q = 0) : d108530 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d108530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7657 q selected
    | true =>
      simp only [d11923, d108530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11924 q = 0) : d108531 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d108531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11924, d108531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11925 q = 0) : d108532 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d108532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11925, d108532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11926 q = 0) : d108533 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11926, d108533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11926, d108533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11927 q = 0) : d108534 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11927, d108534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11927, d108534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11941 q = 0) : d108548 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11941, d108548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11941, d108548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7662 (p : Pattern) (selected : d11942 p = 0) : d108549 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11923 q = 0) : d108530 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d108530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7657 q selected
    | true =>
      simp only [d11923, d108530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11924 q = 0) : d108531 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d108531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11924, d108531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11929 q = 0) : d108536 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11929, d108536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11929, d108536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11930 q = 0) : d108537 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11930, d108537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11930, d108537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11931 q = 0) : d108538 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11931, d108538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11931, d108538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11942 q = 0) : d108549 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11942, d108549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11942, d108549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7663 (p : Pattern) (selected : d11948 p = 0) : d108555 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11933 q = 0) : d108540 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11933, d108540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7658 q selected
    | true =>
      simp only [d11933, d108540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7659 q selected
  have h2 (q : Pattern) (selected : d11934 q = 0) : d108541 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11934, d108541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11934, d108541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11935 q = 0) : d108542 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11935, d108542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11935, d108542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11936 q = 0) : d108543 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11936, d108543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11936, d108543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11937 q = 0) : d108544 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11937, d108544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11937, d108544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11943 q = 0) : d108550 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11943, d108550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7661 q selected
    | true =>
      simp only [d11943, d108550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7662 q selected
  have h7 (q : Pattern) (selected : d11944 q = 0) : d108551 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11944, d108551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11944, d108551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11945 q = 0) : d108552 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11945, d108552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11945, d108552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11946 q = 0) : d108553 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11946, d108553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11946, d108553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11947 q = 0) : d108554 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11947, d108554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11947, d108554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d11948 q = 0) : d108555 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11948, d108555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11948, d108555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro7664 (p : Pattern) (selected : d11953 p = 0) : d108560 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11919 q = 0) : d108526 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d108526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7656 q selected
    | true =>
      simp only [d11919, d108526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11920 q = 0) : d108527 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d108527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11920, d108527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11923 q = 0) : d108530 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d108530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7657 q selected
    | true =>
      simp only [d11923, d108530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11924 q = 0) : d108531 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d108531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11924, d108531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11925 q = 0) : d108532 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d108532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11925, d108532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11926 q = 0) : d108533 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11926, d108533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11926, d108533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11952 q = 0) : d108559 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11952, d108559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11952, d108559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11953 q = 0) : d108560 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11953, d108560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11953, d108560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7665 (p : Pattern) (selected : d11955 p = 0) : d108562 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11923 q = 0) : d108530 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d108530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7657 q selected
    | true =>
      simp only [d11923, d108530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11924 q = 0) : d108531 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d108531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11924, d108531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11929 q = 0) : d108536 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11929, d108536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11929, d108536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11930 q = 0) : d108537 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11930, d108537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11930, d108537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11954 q = 0) : d108561 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11954, d108561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11954, d108561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11955 q = 0) : d108562 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11955, d108562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11955, d108562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7666 (p : Pattern) (selected : d11962 p = 0) : d108569 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11919 q = 0) : d108526 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d108526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7656 q selected
    | true =>
      simp only [d11919, d108526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11920 q = 0) : d108527 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d108527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11920, d108527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11923 q = 0) : d108530 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d108530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7657 q selected
    | true =>
      simp only [d11923, d108530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11924 q = 0) : d108531 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d108531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11924, d108531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11925 q = 0) : d108532 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d108532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11925, d108532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11960 q = 0) : d108567 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11960, d108567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11960, d108567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11961 q = 0) : d108568 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11961, d108568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11961, d108568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11962 q = 0) : d108569 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11962, d108569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11962, d108569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7667 (p : Pattern) (selected : d11965 p = 0) : d108572 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11923 q = 0) : d108530 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d108530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7657 q selected
    | true =>
      simp only [d11923, d108530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11924 q = 0) : d108531 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d108531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11924, d108531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11929 q = 0) : d108536 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11929, d108536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11929, d108536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11963 q = 0) : d108570 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11963, d108570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11963, d108570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11964 q = 0) : d108571 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11964, d108571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11964, d108571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11965 q = 0) : d108572 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11965, d108572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11965, d108572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7668 (p : Pattern) (selected : d11974 p = 0) : d108581 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11969 q = 0) : d108576 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11969, d108576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro577 q selected
    | true =>
      simp only [d11969, d108576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11970 q = 0) : d108577 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11970, d108577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11970, d108577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11971 q = 0) : d108578 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11971, d108578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11971, d108578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11909 q = 0) : d108516 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11909, d108516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro560 q selected
    | true =>
      simp only [d11909, d108516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11910 q = 0) : d108517 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11910, d108517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11910, d108517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11911 q = 0) : d108518 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11911, d108518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11911, d108518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11972 q = 0) : d108579 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11972, d108579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11972, d108579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11912 q = 0) : d108519 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11912, d108519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro561 q selected
    | true =>
      simp only [d11912, d108519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11913 q = 0) : d108520 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11913, d108520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11913, d108520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11914 q = 0) : d108521 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11914, d108521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11914, d108521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d11915 q = 0) : d108522 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11915, d108522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11915, d108522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d11973 q = 0) : d108580 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11973, d108580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11973, d108580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d11974 q = 0) : d108581 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11974, d108581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d11974, d108581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro7669 (p : Pattern) (selected : d11980 p = 0) : d108587 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11975 q = 0) : d108582 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11975, d108582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7668 q selected
    | true =>
      simp only [d11975, d108582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11976 q = 0) : d108583 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11976, d108583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11976, d108583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11919 q = 0) : d108526 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d108526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7656 q selected
    | true =>
      simp only [d11919, d108526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11920 q = 0) : d108527 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d108527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11920, d108527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11977 q = 0) : d108584 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11977, d108584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11977, d108584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11978 q = 0) : d108585 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11978, d108585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11978, d108585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11979 q = 0) : d108586 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11979, d108586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11979, d108586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11980 q = 0) : d108587 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11980, d108587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11980, d108587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7670 (p : Pattern) (selected : d11991 p = 0) : d108525 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11982 q = 0) : d108516 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11982, d108516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro594 q selected
    | true =>
      simp only [d11982, d108516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11983 q = 0) : d108517 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11983, d108517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11983, d108517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11984 q = 0) : d108518 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11984, d108518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11984, d108518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11985 q = 0) : d108519 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11985, d108519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro595 q selected
    | true =>
      simp only [d11985, d108519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11986 q = 0) : d108520 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11986, d108520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11986, d108520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11987 q = 0) : d108521 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11987, d108521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11987, d108521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11988 q = 0) : d108522 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11988, d108522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11988, d108522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11989 q = 0) : d108523 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11989, d108523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11989, d108523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11990 q = 0) : d108524 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11990, d108524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11990, d108524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11991 q = 0) : d108525 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11991, d108525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d11991, d108525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro7671 (p : Pattern) (selected : d11995 p = 0) : d108529 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11985 q = 0) : d108519 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11985, d108519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro595 q selected
    | true =>
      simp only [d11985, d108519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11986 q = 0) : d108520 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11986, d108520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11986, d108520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11987 q = 0) : d108521 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11987, d108521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11987, d108521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11989 q = 0) : d108523 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11989, d108523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11989, d108523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11994 q = 0) : d108528 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11994, d108528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11994, d108528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11995 q = 0) : d108529 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11995, d108529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11995, d108529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7672 (p : Pattern) (selected : d12001 p = 0) : d108535 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11992 q = 0) : d108526 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11992, d108526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7670 q selected
    | true =>
      simp only [d11992, d108526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11993 q = 0) : d108527 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11993, d108527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11993, d108527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11996 q = 0) : d108530 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11996, d108530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7671 q selected
    | true =>
      simp only [d11996, d108530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11997 q = 0) : d108531 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11997, d108531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11997, d108531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11998 q = 0) : d108532 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11998, d108532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11998, d108532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11999 q = 0) : d108533 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11999, d108533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11999, d108533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d12000 q = 0) : d108534 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12000, d108534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d12000, d108534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d12001 q = 0) : d108535 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12001, d108535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12001, d108535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7673 (p : Pattern) (selected : d12005 p = 0) : d108539 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11996 q = 0) : d108530 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11996, d108530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7671 q selected
    | true =>
      simp only [d11996, d108530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11997 q = 0) : d108531 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11997, d108531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11997, d108531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12002 q = 0) : d108536 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12002, d108536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12002, d108536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12003 q = 0) : d108537 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12003, d108537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12003, d108537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12004 q = 0) : d108538 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12004, d108538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12004, d108538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12005 q = 0) : d108539 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12005, d108539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12005, d108539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7674 (p : Pattern) (selected : d12013 p = 0) : d108595 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11909 q = 0) : d108516 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11909, d108516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro560 q selected
    | true =>
      simp only [d11909, d108516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11910 q = 0) : d108517 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11910, d108517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11910, d108517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11911 q = 0) : d108518 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11911, d108518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11911, d108518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11912 q = 0) : d108519 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11912, d108519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro561 q selected
    | true =>
      simp only [d11912, d108519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11913 q = 0) : d108520 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11913, d108520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11913, d108520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11914 q = 0) : d108521 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11914, d108521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11914, d108521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11915 q = 0) : d108522 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11915, d108522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11915, d108522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d12008 q = 0) : d108590 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12008, d108590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3403 q selected
    | true =>
      simp only [d12008, d108590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d12009 q = 0) : d108591 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12009, d108591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12009, d108591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d12010 q = 0) : d108592 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12010, d108592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12010, d108592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d12011 q = 0) : d108593 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12011, d108593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d12011, d108593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d12012 q = 0) : d108594 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12012, d108594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d12012, d108594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d12013 q = 0) : d108595 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12013, d108595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d12013, d108595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro7675 (p : Pattern) (selected : d12019 p = 0) : d108601 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d12014 q = 0) : d108596 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12014, d108596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7674 q selected
    | true =>
      simp only [d12014, d108596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12015 q = 0) : d108597 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12015, d108597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12015, d108597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12016 q = 0) : d108598 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12016, d108598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12016, d108598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12017 q = 0) : d108599 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12017, d108599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12017, d108599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12018 q = 0) : d108600 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12018, d108600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12018, d108600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12019 q = 0) : d108601 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12019, d108601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12019, d108601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7676 (p : Pattern) (selected : d12025 p = 0) : d108607 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11956 q = 0) : d108563 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11956, d108563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7664 q selected
    | true =>
      simp only [d11956, d108563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7665 q selected
  have h2 (q : Pattern) (selected : d11957 q = 0) : d108564 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11957, d108564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11957, d108564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11958 q = 0) : d108565 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11958, d108565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11958, d108565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11959 q = 0) : d108566 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11959, d108566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11959, d108566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11966 q = 0) : d108573 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11966, d108573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7666 q selected
    | true =>
      simp only [d11966, d108573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7667 q selected
  have h6 (q : Pattern) (selected : d11967 q = 0) : d108574 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11967, d108574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11967, d108574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11968 q = 0) : d108575 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11968, d108575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11968, d108575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11981 q = 0) : d108588 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11981, d108588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7669 q selected
    | true =>
      simp only [d11981, d108588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7658 q selected
  have h9 (q : Pattern) (selected : d12006 q = 0) : d108540 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12006, d108540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7672 q selected
    | true =>
      simp only [d12006, d108540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7673 q selected
  have h10 (q : Pattern) (selected : d12007 q = 0) : d108589 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12007, d108589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d12007, d108589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d12020 q = 0) : d108602 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12020, d108602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7675 q selected
    | true =>
      simp only [d12020, d108602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d12021 q = 0) : d108603 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12021, d108603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d12021, d108603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d12022 q = 0) : d108604 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12022, d108604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d12022, d108604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d12023 q = 0) : d108605 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12023, d108605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d12023, d108605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d12024 q = 0) : d108606 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12024, d108606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12024, d108606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d12025 q = 0) : d108607 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12025, d108607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12025, d108607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro7677 (p : Pattern) (selected : d12026 p = 0) : d108608 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11919 q = 0) : d108526 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d108526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7656 q selected
    | true =>
      simp only [d11919, d108526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11920 q = 0) : d108527 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d108527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11920, d108527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11923 q = 0) : d108530 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d108530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7657 q selected
    | true =>
      simp only [d11923, d108530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11924 q = 0) : d108531 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d108531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11924, d108531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11925 q = 0) : d108532 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d108532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11925, d108532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11926 q = 0) : d108533 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11926, d108533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11926, d108533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11952 q = 0) : d108559 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11952, d108559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11952, d108559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d12026 q = 0) : d108608 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12026, d108608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d12026, d108608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7678 (p : Pattern) (selected : d12027 p = 0) : d108609 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11923 q = 0) : d108530 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d108530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7657 q selected
    | true =>
      simp only [d11923, d108530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11924 q = 0) : d108531 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d108531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11924, d108531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11929 q = 0) : d108536 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11929, d108536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11929, d108536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11930 q = 0) : d108537 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11930, d108537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11930, d108537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11954 q = 0) : d108561 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11954, d108561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11954, d108561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d12027 q = 0) : d108609 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12027, d108609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12027, d108609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7679 (p : Pattern) (selected : d12032 p = 0) : d108614 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11919 q = 0) : d108526 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d108526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7656 q selected
    | true =>
      simp only [d11919, d108526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11920 q = 0) : d108527 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d108527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11920, d108527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11923 q = 0) : d108530 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d108530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7657 q selected
    | true =>
      simp only [d11923, d108530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11924 q = 0) : d108531 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d108531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11924, d108531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11925 q = 0) : d108532 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11925, d108532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11925, d108532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11960 q = 0) : d108567 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11960, d108567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11960, d108567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11961 q = 0) : d108568 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11961, d108568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11961, d108568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d12032 q = 0) : d108614 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12032, d108614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d12032, d108614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7680 (p : Pattern) (selected : d12033 p = 0) : d108615 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11923 q = 0) : d108530 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11923, d108530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7657 q selected
    | true =>
      simp only [d11923, d108530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11924 q = 0) : d108531 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11924, d108531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11924, d108531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11929 q = 0) : d108536 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11929, d108536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11929, d108536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11963 q = 0) : d108570 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11963, d108570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11963, d108570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11964 q = 0) : d108571 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11964, d108571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11964, d108571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12033 q = 0) : d108615 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12033, d108615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12033, d108615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7681 (p : Pattern) (selected : d12037 p = 0) : d108619 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11975 q = 0) : d108582 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11975, d108582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7668 q selected
    | true =>
      simp only [d11975, d108582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11976 q = 0) : d108583 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11976, d108583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11976, d108583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11919 q = 0) : d108526 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11919, d108526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7656 q selected
    | true =>
      simp only [d11919, d108526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11920 q = 0) : d108527 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11920, d108527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11920, d108527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11977 q = 0) : d108584 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11977, d108584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11977, d108584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11978 q = 0) : d108585 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11978, d108585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11978, d108585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11979 q = 0) : d108586 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11979, d108586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11979, d108586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d12037 q = 0) : d108619 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12037, d108619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d12037, d108619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7682 (p : Pattern) (selected : d12039 p = 0) : d108548 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11992 q = 0) : d108526 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11992, d108526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7670 q selected
    | true =>
      simp only [d11992, d108526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11993 q = 0) : d108527 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11993, d108527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11993, d108527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11996 q = 0) : d108530 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11996, d108530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7671 q selected
    | true =>
      simp only [d11996, d108530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11997 q = 0) : d108531 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11997, d108531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11997, d108531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11998 q = 0) : d108532 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11998, d108532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11998, d108532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11999 q = 0) : d108533 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11999, d108533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11999, d108533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d12000 q = 0) : d108534 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12000, d108534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d12000, d108534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d12039 q = 0) : d108548 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12039, d108548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d12039, d108548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7683 (p : Pattern) (selected : d12040 p = 0) : d108549 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11996 q = 0) : d108530 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11996, d108530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7671 q selected
    | true =>
      simp only [d11996, d108530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11997 q = 0) : d108531 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11997, d108531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11997, d108531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12002 q = 0) : d108536 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12002, d108536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12002, d108536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12003 q = 0) : d108537 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12003, d108537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12003, d108537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12004 q = 0) : d108538 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12004, d108538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12004, d108538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12040 q = 0) : d108549 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12040, d108549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12040, d108549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7684 (p : Pattern) (selected : d12043 p = 0) : d108622 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d12014 q = 0) : d108596 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12014, d108596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7674 q selected
    | true =>
      simp only [d12014, d108596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12015 q = 0) : d108597 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12015, d108597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12015, d108597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12016 q = 0) : d108598 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12016, d108598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12016, d108598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12017 q = 0) : d108599 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12017, d108599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12017, d108599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12018 q = 0) : d108600 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12018, d108600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12018, d108600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12043 q = 0) : d108622 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12043, d108622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12043, d108622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7685 (p : Pattern) (selected : d12049 p = 0) : d108628 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11956 q = 0) : d108563 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11956, d108563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7664 q selected
    | true =>
      simp only [d11956, d108563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7665 q selected
  have h2 (q : Pattern) (selected : d11957 q = 0) : d108564 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11957, d108564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11957, d108564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11958 q = 0) : d108565 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11958, d108565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11958, d108565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11959 q = 0) : d108566 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11959, d108566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11959, d108566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11966 q = 0) : d108573 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11966, d108573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7666 q selected
    | true =>
      simp only [d11966, d108573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7667 q selected
  have h6 (q : Pattern) (selected : d11967 q = 0) : d108574 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11967, d108574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11967, d108574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11968 q = 0) : d108575 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11968, d108575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11968, d108575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11981 q = 0) : d108588 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11981, d108588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7669 q selected
    | true =>
      simp only [d11981, d108588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7658 q selected
  have h9 (q : Pattern) (selected : d12006 q = 0) : d108540 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12006, d108540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7672 q selected
    | true =>
      simp only [d12006, d108540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7673 q selected
  have h10 (q : Pattern) (selected : d12007 q = 0) : d108589 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12007, d108589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d12007, d108589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d12020 q = 0) : d108602 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12020, d108602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7675 q selected
    | true =>
      simp only [d12020, d108602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d12021 q = 0) : d108603 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12021, d108603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d12021, d108603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d12022 q = 0) : d108604 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12022, d108604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d12022, d108604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d12023 q = 0) : d108605 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12023, d108605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d12023, d108605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d12024 q = 0) : d108606 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12024, d108606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12024, d108606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d12028 q = 0) : d108610 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12028, d108610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7677 q selected
    | true =>
      simp only [d12028, d108610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7678 q selected
  have h17 (q : Pattern) (selected : d12029 q = 0) : d108611 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12029, d108611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12029, d108611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d12030 q = 0) : d108612 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12030, d108612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d12030, d108612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d12031 q = 0) : d108613 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12031, d108613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12031, d108613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d12034 q = 0) : d108616 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12034, d108616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7679 q selected
    | true =>
      simp only [d12034, d108616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7680 q selected
  have h21 (q : Pattern) (selected : d12035 q = 0) : d108617 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12035, d108617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12035, d108617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d12036 q = 0) : d108618 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12036, d108618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d12036, d108618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d12038 q = 0) : d108620 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12038, d108620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7681 q selected
    | true =>
      simp only [d12038, d108620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7661 q selected
  have h24 (q : Pattern) (selected : d12041 q = 0) : d108550 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12041, d108550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7682 q selected
    | true =>
      simp only [d12041, d108550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7683 q selected
  have h25 (q : Pattern) (selected : d12042 q = 0) : d108621 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12042, d108621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d12042, d108621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d12044 q = 0) : d108623 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12044, d108623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7684 q selected
    | true =>
      simp only [d12044, d108623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d12045 q = 0) : d108624 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12045, d108624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d12045, d108624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d12046 q = 0) : d108625 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12046, d108625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d12046, d108625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d12047 q = 0) : d108626 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12047, d108626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d12047, d108626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d12048 q = 0) : d108627 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12048, d108627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d12048, d108627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d12049 q = 0) : d108628 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12049, d108628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d12049, d108628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro7686 (p : Pattern) (selected : d12056 p = 0) : d108635 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11933 q = 0) : d108540 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11933, d108540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7658 q selected
    | true =>
      simp only [d11933, d108540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7659 q selected
  have h2 (q : Pattern) (selected : d11934 q = 0) : d108541 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11934, d108541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11934, d108541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11935 q = 0) : d108542 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11935, d108542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11935, d108542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11936 q = 0) : d108543 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11936, d108543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11936, d108543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11937 q = 0) : d108544 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11937, d108544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11937, d108544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d12051 q = 0) : d108630 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12051, d108630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7659 q selected
    | true =>
      simp only [d12051, d108630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d12052 q = 0) : d108631 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12052, d108631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12052, d108631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d12053 q = 0) : d108632 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12053, d108632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d12053, d108632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d12054 q = 0) : d108633 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12054, d108633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12054, d108633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d12055 q = 0) : d108634 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12055, d108634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12055, d108634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d12056 q = 0) : d108635 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12056, d108635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12056, d108635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro7687 (p : Pattern) (selected : d12062 p = 0) : d108641 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d12051 q = 0) : d108630 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12051, d108630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7659 q selected
    | true =>
      simp only [d12051, d108630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12052 q = 0) : d108631 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12052, d108631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12052, d108631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12053 q = 0) : d108632 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12053, d108632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12053, d108632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12054 q = 0) : d108633 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12054, d108633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12054, d108633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d12055 q = 0) : d108634 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12055, d108634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12055, d108634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d12057 q = 0) : d108636 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12057, d108636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7662 q selected
    | true =>
      simp only [d12057, d108636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d12058 q = 0) : d108637 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12058, d108637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12058, d108637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d12059 q = 0) : d108638 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12059, d108638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d12059, d108638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d12060 q = 0) : d108639 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12060, d108639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12060, d108639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d12061 q = 0) : d108640 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12061, d108640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12061, d108640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d12062 q = 0) : d108641 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12062, d108641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12062, d108641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro7688 (p : Pattern) (selected : d12069 p = 0) : d108648 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d12038 q = 0) : d108620 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12038, d108620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7681 q selected
    | true =>
      simp only [d12038, d108620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7661 q selected
  have h2 (q : Pattern) (selected : d12041 q = 0) : d108550 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12041, d108550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7682 q selected
    | true =>
      simp only [d12041, d108550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7683 q selected
  have h3 (q : Pattern) (selected : d12042 q = 0) : d108621 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12042, d108621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12042, d108621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d12044 q = 0) : d108623 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12044, d108623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7684 q selected
    | true =>
      simp only [d12044, d108623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12045 q = 0) : d108624 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12045, d108624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12045, d108624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12046 q = 0) : d108625 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12046, d108625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12046, d108625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d12067 q = 0) : d108646 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12067, d108646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12067, d108646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d12068 q = 0) : d108647 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12068, d108647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12068, d108647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d12069 q = 0) : d108648 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12069, d108648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12069, d108648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7689 (p : Pattern) (selected : d12071 p = 0) : d108650 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d12057 q = 0) : d108636 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12057, d108636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7662 q selected
    | true =>
      simp only [d12057, d108636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12058 q = 0) : d108637 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12058, d108637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12058, d108637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12059 q = 0) : d108638 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12059, d108638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12059, d108638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12060 q = 0) : d108639 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12060, d108639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12060, d108639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d12061 q = 0) : d108640 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12061, d108640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12061, d108640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d12071 q = 0) : d108650 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12071, d108650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12071, d108650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7690 (p : Pattern) (selected : d12089 p = 0) : d108668 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d12077 q = 0) : d108656 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12077, d108656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro615 q selected
    | true =>
      simp only [d12077, d108656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12078 q = 0) : d108657 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12078, d108657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12078, d108657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12079 q = 0) : d108658 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12079, d108658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12079, d108658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d12080 q = 0) : d108659 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12080, d108659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro616 q selected
    | true =>
      simp only [d12080, d108659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12081 q = 0) : d108660 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12081, d108660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12081, d108660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d12082 q = 0) : d108661 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12082, d108661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12082, d108661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d12083 q = 0) : d108662 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12083, d108662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12083, d108662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d12084 q = 0) : d108663 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12084, d108663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro617 q selected
    | true =>
      simp only [d12084, d108663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d12085 q = 0) : d108664 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12085, d108664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12085, d108664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d12086 q = 0) : d108665 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12086, d108665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12086, d108665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d12087 q = 0) : d108666 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12087, d108666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d12087, d108666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d12088 q = 0) : d108667 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12088, d108667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d12088, d108667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d12089 q = 0) : d108668 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12089, d108668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d12089, d108668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro7691 (p : Pattern) (selected : d12094 p = 0) : d108673 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d12080 q = 0) : d108659 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12080, d108659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro616 q selected
    | true =>
      simp only [d12080, d108659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12081 q = 0) : d108660 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12081, d108660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12081, d108660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12082 q = 0) : d108661 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12082, d108661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12082, d108661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d12084 q = 0) : d108663 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12084, d108663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro617 q selected
    | true =>
      simp only [d12084, d108663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12085 q = 0) : d108664 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12085, d108664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12085, d108664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d12086 q = 0) : d108665 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12086, d108665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12086, d108665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d12087 q = 0) : d108666 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12087, d108666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12087, d108666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d12092 q = 0) : d108671 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12092, d108671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d12092, d108671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d12093 q = 0) : d108672 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12093, d108672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d12093, d108672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d12094 q = 0) : d108673 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12094, d108673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d12094, d108673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro7692 (p : Pattern) (selected : d12100 p = 0) : d108679 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d12090 q = 0) : d108669 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12090, d108669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7690 q selected
    | true =>
      simp only [d12090, d108669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12091 q = 0) : d108670 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12091, d108670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12091, d108670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12095 q = 0) : d108674 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12095, d108674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7691 q selected
    | true =>
      simp only [d12095, d108674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12096 q = 0) : d108675 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12096, d108675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12096, d108675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d12097 q = 0) : d108676 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12097, d108676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12097, d108676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d12098 q = 0) : d108677 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12098, d108677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12098, d108677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d12099 q = 0) : d108678 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12099, d108678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d12099, d108678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d12100 q = 0) : d108679 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12100, d108679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d12100, d108679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7693 (p : Pattern) (selected : d12102 p = 0) : d108681 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d12084 q = 0) : d108663 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12084, d108663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro617 q selected
    | true =>
      simp only [d12084, d108663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12085 q = 0) : d108664 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12085, d108664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12085, d108664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12086 q = 0) : d108665 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12086, d108665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12086, d108665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d12092 q = 0) : d108671 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12092, d108671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12092, d108671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12101 q = 0) : d108680 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12101, d108680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12101, d108680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12102 q = 0) : d108681 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12102, d108681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12102, d108681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7694 (p : Pattern) (selected : d12108 p = 0) : d108687 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d12095 q = 0) : d108674 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12095, d108674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7691 q selected
    | true =>
      simp only [d12095, d108674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12096 q = 0) : d108675 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12096, d108675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12096, d108675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12103 q = 0) : d108682 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12103, d108682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7693 q selected
    | true =>
      simp only [d12103, d108682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12104 q = 0) : d108683 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12104, d108683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12104, d108683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d12105 q = 0) : d108684 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12105, d108684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12105, d108684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d12106 q = 0) : d108685 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12106, d108685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12106, d108685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d12107 q = 0) : d108686 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12107, d108686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d12107, d108686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d12108 q = 0) : d108687 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12108, d108687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d12108, d108687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7695 (p : Pattern) (selected : d12119 p = 0) : d108673 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d12110 q = 0) : d108659 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12110, d108659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro624 q selected
    | true =>
      simp only [d12110, d108659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12111 q = 0) : d108660 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12111, d108660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12111, d108660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12112 q = 0) : d108661 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12112, d108661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12112, d108661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d12113 q = 0) : d108663 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12113, d108663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro625 q selected
    | true =>
      simp only [d12113, d108663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12114 q = 0) : d108664 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12114, d108664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12114, d108664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d12115 q = 0) : d108665 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12115, d108665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12115, d108665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d12116 q = 0) : d108666 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12116, d108666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12116, d108666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d12117 q = 0) : d108671 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12117, d108671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d12117, d108671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d12118 q = 0) : d108672 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12118, d108672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d12118, d108672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d12119 q = 0) : d108673 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12119, d108673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d12119, d108673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro7696 (p : Pattern) (selected : d12123 p = 0) : d108681 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d12113 q = 0) : d108663 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12113, d108663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro625 q selected
    | true =>
      simp only [d12113, d108663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12114 q = 0) : d108664 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12114, d108664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12114, d108664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12115 q = 0) : d108665 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12115, d108665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12115, d108665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d12117 q = 0) : d108671 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12117, d108671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12117, d108671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12122 q = 0) : d108680 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12122, d108680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12122, d108680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12123 q = 0) : d108681 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12123, d108681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12123, d108681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7697 (p : Pattern) (selected : d12129 p = 0) : d108687 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d12120 q = 0) : d108674 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12120, d108674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7695 q selected
    | true =>
      simp only [d12120, d108674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12121 q = 0) : d108675 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12121, d108675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12121, d108675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12124 q = 0) : d108682 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12124, d108682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7696 q selected
    | true =>
      simp only [d12124, d108682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12125 q = 0) : d108683 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12125, d108683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12125, d108683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d12126 q = 0) : d108684 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12126, d108684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12126, d108684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d12127 q = 0) : d108685 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12127, d108685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12127, d108685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d12128 q = 0) : d108686 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12128, d108686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d12128, d108686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d12129 q = 0) : d108687 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12129, d108687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d12129, d108687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7698 (p : Pattern) (selected : d12133 p = 0) : d108692 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d12124 q = 0) : d108682 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12124, d108682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7696 q selected
    | true =>
      simp only [d12124, d108682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12125 q = 0) : d108683 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12125, d108683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12125, d108683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12130 q = 0) : d108689 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12130, d108689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12130, d108689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12131 q = 0) : d108690 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12131, d108690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12131, d108690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12132 q = 0) : d108691 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12132, d108691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12132, d108691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12133 q = 0) : d108692 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12133, d108692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12133, d108692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7699 (p : Pattern) (selected : d12141 p = 0) : d108700 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d12080 q = 0) : d108659 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12080, d108659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro616 q selected
    | true =>
      simp only [d12080, d108659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12081 q = 0) : d108660 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12081, d108660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12081, d108660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12082 q = 0) : d108661 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12082, d108661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12082, d108661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d12084 q = 0) : d108663 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12084, d108663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro617 q selected
    | true =>
      simp only [d12084, d108663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12085 q = 0) : d108664 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12085, d108664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12085, d108664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d12086 q = 0) : d108665 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12086, d108665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12086, d108665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d12087 q = 0) : d108666 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12087, d108666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12087, d108666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d12136 q = 0) : d108695 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d12136, d108695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3411 q selected
    | true =>
      simp only [d12136, d108695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d12137 q = 0) : d108696 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d12137, d108696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12137, d108696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d12138 q = 0) : d108697 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d12138, d108697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12138, d108697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d12139 q = 0) : d108698 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d12139, d108698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d12139, d108698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d12140 q = 0) : d108699 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d12140, d108699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d12140, d108699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d12141 q = 0) : d108700 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d12141, d108700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d12141, d108700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro7700 (p : Pattern) (selected : d12147 p = 0) : d108706 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d12142 q = 0) : d108701 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12142, d108701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7699 q selected
    | true =>
      simp only [d12142, d108701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12143 q = 0) : d108702 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12143, d108702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12143, d108702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12144 q = 0) : d108703 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12144, d108703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12144, d108703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12145 q = 0) : d108704 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12145, d108704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12145, d108704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12146 q = 0) : d108705 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12146, d108705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12146, d108705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12147 q = 0) : d108706 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12147, d108706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12147, d108706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7701 (p : Pattern) (selected : d12153 p = 0) : d108712 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d12109 q = 0) : d108688 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12109, d108688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7692 q selected
    | true =>
      simp only [d12109, d108688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7694 q selected
  have h2 (q : Pattern) (selected : d12134 q = 0) : d108693 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12134, d108693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7697 q selected
    | true =>
      simp only [d12134, d108693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7698 q selected
  have h3 (q : Pattern) (selected : d12135 q = 0) : d108694 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12135, d108694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12135, d108694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d12148 q = 0) : d108707 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12148, d108707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7700 q selected
    | true =>
      simp only [d12148, d108707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12149 q = 0) : d108708 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12149, d108708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12149, d108708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12150 q = 0) : d108709 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12150, d108709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12150, d108709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d12151 q = 0) : d108710 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12151, d108710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12151, d108710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d12152 q = 0) : d108711 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12152, d108711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12152, d108711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d12153 q = 0) : d108712 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12153, d108712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12153, d108712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7702 (p : Pattern) (selected : d12158 p = 0) : d108692 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d12103 q = 0) : d108682 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d12103, d108682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7693 q selected
    | true =>
      simp only [d12103, d108682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12104 q = 0) : d108683 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d12104, d108683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12104, d108683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12155 q = 0) : d108689 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d12155, d108689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12155, d108689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12156 q = 0) : d108690 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d12156, d108690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12156, d108690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12157 q = 0) : d108691 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d12157, d108691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12157, d108691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12158 q = 0) : d108692 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d12158, d108692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12158, d108692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7703 (p : Pattern) (selected : d12164 p = 0) : d108719 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d12159 q = 0) : d108714 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12159, d108714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7702 q selected
    | true =>
      simp only [d12159, d108714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12160 q = 0) : d108715 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12160, d108715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12160, d108715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12161 q = 0) : d108716 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12161, d108716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12161, d108716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12162 q = 0) : d108717 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12162, d108717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12162, d108717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d12163 q = 0) : d108718 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12163, d108718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12163, d108718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d12164 q = 0) : d108719 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d12164, d108719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12164, d108719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7704 (p : Pattern) (selected : d12170 p = 0) : d108725 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11939 q = 0) : d108546 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11939, d108546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11939, d108546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7660 q selected
  have h2 (q : Pattern) (selected : d11940 q = 0) : d108547 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11940, d108547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d11940, d108547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d11949 q = 0) : d108556 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11949, d108556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7660 q selected
    | true =>
      simp only [d11949, d108556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7663 q selected
  have h4 (q : Pattern) (selected : d11950 q = 0) : d108557 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11950, d108557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11950, d108557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11951 q = 0) : d108558 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11951, d108558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11951, d108558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d12050 q = 0) : d108629 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12050, d108629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7676 q selected
    | true =>
      simp only [d12050, d108629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7685 q selected
  have h7 (q : Pattern) (selected : d12063 q = 0) : d108642 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12063, d108642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7686 q selected
    | true =>
      simp only [d12063, d108642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7687 q selected
  have h8 (q : Pattern) (selected : d12064 q = 0) : d108643 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12064, d108643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d12064, d108643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d12065 q = 0) : d108644 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d12065, d108644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d12065, d108644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d12066 q = 0) : d108645 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d12066, d108645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12066, d108645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d12070 q = 0) : d108649 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12070, d108649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12070, d108649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7688 q selected
  have h12 (q : Pattern) (selected : d12072 q = 0) : d108651 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12072, d108651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12072, d108651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7689 q selected
  have h13 (q : Pattern) (selected : d12073 q = 0) : d108652 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12073, d108652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d12073, d108652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d12074 q = 0) : d108653 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d12074, d108653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d12074, d108653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d12075 q = 0) : d108654 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d12075, d108654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d12075, d108654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d12076 q = 0) : d108655 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d12076, d108655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d12076, d108655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d12154 q = 0) : d108713 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12154, d108713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12154, d108713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7701 q selected
  have h18 (q : Pattern) (selected : d12165 q = 0) : d108720 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12165, d108720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12165, d108720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7703 q selected
  have h19 (q : Pattern) (selected : d12166 q = 0) : d108721 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12166, d108721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d12166, d108721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d12167 q = 0) : d108722 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d12167, d108722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d12167, d108722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d12168 q = 0) : d108723 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d12168, d108723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d12168, d108723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d12169 q = 0) : d108724 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d12169, d108724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d12169, d108724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d12170 q = 0) : d108725 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d12170, d108725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d12170, d108725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro7705 (p : Pattern) (selected : d12176 p = 0) : d108731 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d12171 q = 0) : d108726 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d12171, d108726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12171, d108726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7704 q selected
  have h2 (q : Pattern) (selected : d12172 q = 0) : d108727 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d12172, d108727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12172, d108727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d12173 q = 0) : d108728 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d12173, d108728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12173, d108728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d12174 q = 0) : d108729 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d12174, d108729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12174, d108729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d12175 q = 0) : d108730 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d12175, d108730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12175, d108730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d12176 q = 0) : d108731 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d12176, d108731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d12176, d108731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7706 (p : Pattern) (selected : d12182 p = 0) : d108737 p = 1 := by
  have h0 (q : Pattern) (selected : d11095 q = 0) : d107858 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d11095, d107858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7457 q selected
    | true =>
      simp only [d11095, d107858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7505 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d11364 q = 0) : d108075 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d11364, d108075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d11364, d108075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7555 q selected
  have h3 (q : Pattern) (selected : d11365 q = 0) : d108076 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d11365, d108076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11365, d108076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11634 q = 0) : d108293 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d11634, d108293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d11634, d108293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7605 q selected
  have h5 (q : Pattern) (selected : d11635 q = 0) : d108294 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d11635, d108294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d11635, d108294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11636 q = 0) : d108295 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d11636, d108295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11636, d108295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11905 q = 0) : d108512 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d11905, d108512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d11905, d108512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7655 q selected
  have h8 (q : Pattern) (selected : d11906 q = 0) : d108513 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d11906, d108513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d11906, d108513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d11907 q = 0) : d108514 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d11907, d108514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d11907, d108514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11908 q = 0) : d108515 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d11908, d108515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11908, d108515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d12177 q = 0) : d108732 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d12177, d108732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12177, d108732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7705 q selected
  have h12 (q : Pattern) (selected : d12178 q = 0) : d108733 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d12178, d108733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12178, d108733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d12179 q = 0) : d108734 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d12179, d108734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12179, d108734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d12180 q = 0) : d108735 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d12180, d108735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12180, d108735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d12181 q = 0) : d108736 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d12181, d108736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d12181, d108736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d12182 q = 0) : d108737 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d12182, d108737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d12182, d108737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro7707 (p : Pattern) (selected : d12188 p = 0) : d108743 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d12183 q = 0) : d108738 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d12183, d108738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7706 q selected
    | true =>
      simp only [d12183, d108738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12184 q = 0) : d108739 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d12184, d108739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12184, d108739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d12185 q = 0) : d108740 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d12185, d108740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12185, d108740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12186 q = 0) : d108741 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d12186, d108741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12186, d108741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12187 q = 0) : d108742 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d12187, d108742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12187, d108742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12188 q = 0) : d108743 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d12188, d108743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12188, d108743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7708 (p : Pattern) (selected : d12194 p = 0) : d108749 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d12189 q = 0) : d108744 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d12189, d108744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7707 q selected
    | true =>
      simp only [d12189, d108744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12190 q = 0) : d108745 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d12190, d108745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12190, d108745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d12191 q = 0) : d108746 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d12191, d108746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12191, d108746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12192 q = 0) : d108747 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d12192, d108747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12192, d108747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12193 q = 0) : d108748 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d12193, d108748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12193, d108748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12194 q = 0) : d108749 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d12194, d108749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12194, d108749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7709 (p : Pattern) (selected : d12200 p = 0) : d108755 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d12195 q = 0) : d108750 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d12195, d108750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7708 q selected
    | true =>
      simp only [d12195, d108750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12196 q = 0) : d108751 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d12196, d108751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12196, d108751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d12197 q = 0) : d108752 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d12197, d108752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12197, d108752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12198 q = 0) : d108753 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d12198, d108753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12198, d108753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12199 q = 0) : d108754 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d12199, d108754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12199, d108754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12200 q = 0) : d108755 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d12200, d108755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12200, d108755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7710 (p : Pattern) (selected : d12206 p = 0) : d108761 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d12201 q = 0) : d108756 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d12201, d108756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7709 q selected
    | true =>
      simp only [d12201, d108756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12202 q = 0) : d108757 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d12202, d108757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12202, d108757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d12203 q = 0) : d108758 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d12203, d108758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12203, d108758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12204 q = 0) : d108759 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d12204, d108759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12204, d108759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12205 q = 0) : d108760 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d12205, d108760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12205, d108760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12206 q = 0) : d108761 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d12206, d108761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12206, d108761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7711 (p : Pattern) (selected : d12212 p = 0) : d108767 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d12207 q = 0) : d108762 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d12207, d108762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7710 q selected
    | true =>
      simp only [d12207, d108762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12208 q = 0) : d108763 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d12208, d108763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12208, d108763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d12209 q = 0) : d108764 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d12209, d108764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12209, d108764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12210 q = 0) : d108765 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d12210, d108765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12210, d108765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12211 q = 0) : d108766 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d12211, d108766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12211, d108766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12212 q = 0) : d108767 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d12212, d108767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12212, d108767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7712 (p : Pattern) (selected : d12218 p = 0) : d108773 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d12213 q = 0) : d108768 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d12213, d108768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7711 q selected
    | true =>
      simp only [d12213, d108768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12214 q = 0) : d108769 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d12214, d108769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12214, d108769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d12215 q = 0) : d108770 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d12215, d108770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12215, d108770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12216 q = 0) : d108771 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d12216, d108771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12216, d108771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12217 q = 0) : d108772 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d12217, d108772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12217, d108772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12218 q = 0) : d108773 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d12218, d108773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12218, d108773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7713 (p : Pattern) (selected : d12224 p = 0) : d108779 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d12219 q = 0) : d108774 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d12219, d108774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7712 q selected
    | true =>
      simp only [d12219, d108774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d12220 q = 0) : d108775 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d12220, d108775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d12220, d108775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d12221 q = 0) : d108776 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d12221, d108776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d12221, d108776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d12222 q = 0) : d108777 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d12222, d108777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d12222, d108777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d12223 q = 0) : d108778 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d12223, d108778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d12223, d108778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d12224 q = 0) : d108779 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d12224, d108779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d12224, d108779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7714 (p : Pattern) (selected : d10666 p = 1) : d108784 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d120 q = 1) : d120 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d126 q = 1) : d126 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d10661 q = 1) : d10661 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d188 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4 q selected
    | true =>
      simp only [d188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10662 q = 1) : d108780 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10662, d108780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10662, d108780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44 q = 1) : d44 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d10663 q = 1) : d108781 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10663, d108781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10663, d108781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10664 q = 1) : d108782 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10664, d108782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10664, d108782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10665 q = 1) : d108783 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10665, d108783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10665, d108783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10666 q = 1) : d108784 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10666, d108784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10666, d108784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro7715 (p : Pattern) (selected : d10673 p = 1) : d108789 p = 1 := by
  have h0 (q : Pattern) (selected : d120 q = 1) : d120 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d126 q = 1) : d126 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d10661 q = 1) : d10661 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d188 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4 q selected
    | true =>
      simp only [d188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10662 q = 1) : d108780 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10662, d108780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10662, d108780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44 q = 1) : d44 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d10663 q = 1) : d108781 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10663, d108781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10663, d108781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10664 q = 1) : d108782 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10664, d108782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10664, d108782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10665 q = 1) : d108783 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10665, d108783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10665, d108783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d198 q = 1) : d198 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d202 q = 1) : d202 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d10668 q = 1) : d10668 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d206 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6 q selected
    | true =>
      simp only [d206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h14 (q : Pattern) (selected : d10669 q = 1) : d108785 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10669, d108785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d10669, d108785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d51 q = 1) : d51 q = 1 := by
    exact selected
  have h16 (q : Pattern) (selected : d10670 q = 1) : d108786 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10670, d108786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d10670, d108786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d10671 q = 1) : d108787 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10671, d108787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d10671, d108787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d10672 q = 1) : d108788 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10672, d108788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d10672, d108788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d10673 q = 1) : d108789 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10673, d108789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10673, d108789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro7716 (p : Pattern) (selected : d10680 p = 1) : d108796 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10668 q = 1) : d10668 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d206 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6 q selected
    | true =>
      simp only [d206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10669 q = 1) : d108785 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10669, d108785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10669, d108785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d51 q = 1) : d51 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d10670 q = 1) : d108786 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10670, d108786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10670, d108786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10678 q = 1) : d108794 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10678, d108794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10678, d108794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10679 q = 1) : d108795 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10679, d108795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10679, d108795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10680 q = 1) : d108796 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10680, d108796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10680, d108796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7717 (p : Pattern) (selected : d10703 p = 1) : d108806 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10698 q = 1) : d10698 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d263 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11 q selected
    | true =>
      simp only [d263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10699 q = 1) : d108802 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10699, d108802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10699, d108802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d85 q = 1) : d85 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d10700 q = 1) : d108803 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10700, d108803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10700, d108803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10701 q = 1) : d108804 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10701, d108804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10701, d108804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10702 q = 1) : d108805 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10702, d108805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10702, d108805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10703 q = 1) : d108806 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10703, d108806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10703, d108806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7718 (p : Pattern) (selected : d10709 p = 1) : d108812 p = 1 := by
  have h0 (q : Pattern) (selected : d114 q = 1) : d114 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10674 q = 1) : d108790 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10674, d108790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7714 q selected
    | true =>
      simp only [d10674, d108790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7715 q selected
  have h2 (q : Pattern) (selected : d214 q = 1) : d214 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d10675 q = 1) : d108791 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10675, d108791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10675, d108791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d10676 q = 1) : d108792 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d10676, d108792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10676, d108792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10677 q = 1) : d108793 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d10677, d108793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10677, d108793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10681 q = 1) : d108797 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10681, d108797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10681, d108797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7716 q selected
  have h8 (q : Pattern) (selected : d10682 q = 1) : d108798 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10682, d108798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10682, d108798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d10683 q = 1) : d108799 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d10683, d108799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10683, d108799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d10684 q = 1) : d108800 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d10684, d108800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10684, d108800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d10685 q = 1) : d108801 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d10685, d108801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10685, d108801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d10704 q = 1) : d108807 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10704, d108807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10704, d108807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7717 q selected
  have h13 (q : Pattern) (selected : d10705 q = 1) : d108808 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10705, d108808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d10705, d108808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d10706 q = 1) : d108809 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d10706, d108809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d10706, d108809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d10707 q = 1) : d108810 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d10707, d108810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d10707, d108810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d10708 q = 1) : d108811 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d10708, d108811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d10708, d108811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d10709 q = 1) : d108812 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d10709, d108812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d10709, d108812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro7719 (p : Pattern) (selected : d10760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10755 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16 q selected
    | true =>
      simp only [d10755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10756 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10757 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2 q selected
    | true =>
      simp only [d176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d177 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d178 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10758 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d179 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10759 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10760 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro7720 (p : Pattern) (selected : d10766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10761 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7719 q selected
    | true =>
      simp only [d10761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10762 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3 q selected
    | true =>
      simp only [d182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d183 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10763 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10764 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10765 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10766 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7721 (p : Pattern) (selected : d10778 p = 1) : d108822 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10735 q = 1) : d10735 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d10741 q = 1) : d10741 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d10754 q = 1) : d10754 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d10767 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7720 q selected
    | true =>
      simp only [d10767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4 q selected
  have h5 (q : Pattern) (selected : d10768 q = 1) : d108818 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10768, d108818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10768, d108818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10774 q = 1) : d10774 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d10775 q = 1) : d108819 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10775, d108819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10775, d108819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10776 q = 1) : d108820 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10776, d108820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10776, d108820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10777 q = 1) : d108821 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10777, d108821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10777, d108821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10778 q = 1) : d108822 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10778, d108822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10778, d108822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro7722 (p : Pattern) (selected : d10790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10761 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7719 q selected
    | true =>
      simp only [d10761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10762 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3 q selected
    | true =>
      simp only [d182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d183 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10763 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10764 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10765 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10790 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7723 (p : Pattern) (selected : d10799 p = 1) : d108827 p = 1 := by
  have h0 (q : Pattern) (selected : d10735 q = 1) : d10735 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10741 q = 1) : d10741 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d10754 q = 1) : d10754 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d10767 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7720 q selected
    | true =>
      simp only [d10767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4 q selected
  have h4 (q : Pattern) (selected : d10768 q = 1) : d108818 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10768, d108818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10768, d108818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10774 q = 1) : d10774 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d10775 q = 1) : d108819 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10775, d108819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10775, d108819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10776 q = 1) : d108820 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10776, d108820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10776, d108820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10777 q = 1) : d108821 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10777, d108821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10777, d108821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10783 q = 1) : d10783 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d10787 q = 1) : d10787 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d10789 q = 1) : d10789 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d10791 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7722 q selected
    | true =>
      simp only [d10791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6 q selected
  have h13 (q : Pattern) (selected : d10792 q = 1) : d108823 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10792, d108823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d10792, d108823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d10795 q = 1) : d10795 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d10796 q = 1) : d108824 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10796, d108824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d10796, d108824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d10797 q = 1) : d108825 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10797, d108825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d10797, d108825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d10798 q = 1) : d108826 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10798, d108826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10798, d108826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d10799 q = 1) : d108827 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10799, d108827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10799, d108827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro7724 (p : Pattern) (selected : d10808 p = 1) : d108834 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10789 q = 1) : d10789 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d10791 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7722 q selected
    | true =>
      simp only [d10791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6 q selected
  have h3 (q : Pattern) (selected : d10792 q = 1) : d108823 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10792, d108823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10792, d108823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10795 q = 1) : d10795 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d10796 q = 1) : d108824 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10796, d108824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10796, d108824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10806 q = 1) : d108832 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10806, d108832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10806, d108832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10807 q = 1) : d108833 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10807, d108833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10807, d108833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10808 q = 1) : d108834 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10808, d108834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10808, d108834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7725 (p : Pattern) (selected : d10832 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10827 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23 q selected
    | true =>
      simp only [d10827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10828 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10829 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
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
  have h7 (q : Pattern) (selected : d10830 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
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
  have h9 (q : Pattern) (selected : d10831 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10832 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro7726 (p : Pattern) (selected : d10838 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10833 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7725 q selected
    | true =>
      simp only [d10833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10834 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d257 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10 q selected
    | true =>
      simp only [d257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d258 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10835 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10836 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10837 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10838 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7727 (p : Pattern) (selected : d10850 p = 1) : d108844 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10826 q = 1) : d10826 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d10839 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7726 q selected
    | true =>
      simp only [d10839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11 q selected
  have h3 (q : Pattern) (selected : d10840 q = 1) : d108840 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10840, d108840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10840, d108840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10846 q = 1) : d10846 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d10847 q = 1) : d108841 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10847, d108841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10847, d108841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10848 q = 1) : d108842 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10848, d108842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10848, d108842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10849 q = 1) : d108843 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10849, d108843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10849, d108843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10850 q = 1) : d108844 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10850, d108844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10850, d108844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7728 (p : Pattern) (selected : d10856 p = 1) : d108850 p = 1 := by
  have h0 (q : Pattern) (selected : d10729 q = 1) : d10729 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10800 q = 1) : d108828 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10800, d108828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7721 q selected
    | true =>
      simp only [d10800, d108828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7723 q selected
  have h2 (q : Pattern) (selected : d10802 q = 1) : d10802 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d10803 q = 1) : d108829 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10803, d108829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10803, d108829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d10804 q = 1) : d108830 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d10804, d108830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10804, d108830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10805 q = 1) : d108831 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d10805, d108831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10805, d108831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10809 q = 1) : d108835 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10809, d108835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10809, d108835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7724 q selected
  have h8 (q : Pattern) (selected : d407 q = 1) : d407 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d10810 q = 1) : d108836 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10810, d108836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10810, d108836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10811 q = 1) : d108837 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d10811, d108837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10811, d108837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d10812 q = 1) : d108838 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d10812, d108838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d10812, d108838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d10813 q = 1) : d108839 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d10813, d108839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10813, d108839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d10851 q = 1) : d108845 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10851, d108845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10851, d108845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7727 q selected
  have h14 (q : Pattern) (selected : d463 q = 1) : d463 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d10852 q = 1) : d108846 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10852, d108846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d10852, d108846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d10853 q = 1) : d108847 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d10853, d108847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d10853, d108847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d10854 q = 1) : d108848 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d10854, d108848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d10854, d108848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d10855 q = 1) : d108849 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d10855, d108849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d10855, d108849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d10856 q = 1) : d108850 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d10856, d108850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d10856, d108850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro7729 (p : Pattern) (selected : d10862 p = 1) : d108856 p = 1 := by
  have h0 (q : Pattern) (selected : d99 q = 1) : d99 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d10710 q = 1) : d108813 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d10710, d108813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10710, d108813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7718 q selected
  have h3 (q : Pattern) (selected : d10711 q = 1) : d108814 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d10711, d108814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10711, d108814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10712 q = 1) : d108815 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d10712, d108815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10712, d108815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10713 q = 1) : d108816 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d10713, d108816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10713, d108816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10714 q = 1) : d108817 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d10714, d108817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10714, d108817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10857 q = 1) : d108851 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d10857, d108851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10857, d108851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7728 q selected
  have h8 (q : Pattern) (selected : d10858 q = 1) : d108852 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d10858, d108852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10858, d108852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10859 q = 1) : d108853 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d10859, d108853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10859, d108853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10860 q = 1) : d108854 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d10860, d108854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10860, d108854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10861 q = 1) : d108855 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d10861, d108855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10861, d108855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d10862 q = 1) : d108856 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d10862, d108856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10862, d108856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro7730 (p : Pattern) (selected : d10935 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10929 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro31 q selected
    | true =>
      simp only [d10929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10930 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10931 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10755 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16 q selected
    | true =>
      simp only [d10755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10756 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10757 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10932 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10933 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10934 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10935 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro7731 (p : Pattern) (selected : d10939 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10755 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16 q selected
    | true =>
      simp only [d10755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10756 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10757 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10933 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10938 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10939 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7732 (p : Pattern) (selected : d10945 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10936 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7730 q selected
    | true =>
      simp only [d10936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10937 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10940 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7731 q selected
    | true =>
      simp only [d10940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10942 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10943 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10944 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10945 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7733 (p : Pattern) (selected : d10949 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10940 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7731 q selected
    | true =>
      simp only [d10940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10946 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10947 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10948 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10949 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7734 (p : Pattern) (selected : d10961 p = 1) : d108861 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10906 q = 1) : d10906 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d10915 q = 1) : d10915 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d10928 q = 1) : d10928 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d10950 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7732 q selected
    | true =>
      simp only [d10950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7733 q selected
  have h5 (q : Pattern) (selected : d10951 q = 1) : d108857 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10951, d108857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10951, d108857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10957 q = 1) : d10957 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d10958 q = 1) : d108858 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10958, d108858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10958, d108858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10959 q = 1) : d108859 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10959, d108859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10959, d108859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10960 q = 1) : d108860 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10960, d108860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10960, d108860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10961 q = 1) : d108861 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10961, d108861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10961, d108861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro7735 (p : Pattern) (selected : d10975 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10936 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7730 q selected
    | true =>
      simp only [d10936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10937 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10940 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7731 q selected
    | true =>
      simp only [d10940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10942 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10943 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10944 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10975 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7736 (p : Pattern) (selected : d10976 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10940 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7731 q selected
    | true =>
      simp only [d10940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10941 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10946 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10947 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10948 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10976 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7737 (p : Pattern) (selected : d10985 p = 1) : d108866 p = 1 := by
  have h0 (q : Pattern) (selected : d10906 q = 1) : d10906 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10915 q = 1) : d10915 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d10928 q = 1) : d10928 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d10950 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7732 q selected
    | true =>
      simp only [d10950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7733 q selected
  have h4 (q : Pattern) (selected : d10951 q = 1) : d108857 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10951, d108857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10951, d108857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10957 q = 1) : d10957 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d10958 q = 1) : d108858 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10958, d108858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10958, d108858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10959 q = 1) : d108859 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10959, d108859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10959, d108859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10960 q = 1) : d108860 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10960, d108860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10960, d108860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10967 q = 1) : d10967 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d10972 q = 1) : d10972 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d10974 q = 1) : d10974 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d10977 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7735 q selected
    | true =>
      simp only [d10977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7736 q selected
  have h13 (q : Pattern) (selected : d10978 q = 1) : d108862 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10978, d108862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d10978, d108862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d10981 q = 1) : d10981 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d10982 q = 1) : d108863 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10982, d108863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d10982, d108863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d10983 q = 1) : d108864 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10983, d108864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d10983, d108864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d10984 q = 1) : d108865 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10984, d108865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10984, d108865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d10985 q = 1) : d108866 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10985, d108866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10985, d108866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro7738 (p : Pattern) (selected : d11005 p = 1) : d108873 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10974 q = 1) : d10974 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d10977 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7735 q selected
    | true =>
      simp only [d10977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7736 q selected
  have h3 (q : Pattern) (selected : d10978 q = 1) : d108862 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10978, d108862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10978, d108862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10981 q = 1) : d10981 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d10982 q = 1) : d108863 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10982, d108863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10982, d108863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11003 q = 1) : d108871 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11003, d108871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11003, d108871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11004 q = 1) : d108872 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11004, d108872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11004, d108872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11005 q = 1) : d108873 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11005, d108873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11005, d108873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7739 (p : Pattern) (selected : d11045 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11039 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro41 q selected
    | true =>
      simp only [d11039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11040 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11041 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10827 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23 q selected
    | true =>
      simp only [d10827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10828 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10829 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11042 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11043 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11044 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11045 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d11045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro7740 (p : Pattern) (selected : d11049 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10827 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro23 q selected
    | true =>
      simp only [d10827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10828 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10829 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11043 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11048 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11049 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7741 (p : Pattern) (selected : d11055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11046 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7739 q selected
    | true =>
      simp only [d11046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11047 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11050 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7740 q selected
    | true =>
      simp only [d11050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11051 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11052 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11053 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11054 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11055 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7742 (p : Pattern) (selected : d11059 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11050 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7740 q selected
    | true =>
      simp only [d11050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11051 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11056 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11057 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11058 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11059 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7743 (p : Pattern) (selected : d11071 p = 1) : d108883 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11038 q = 1) : d11038 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d11060 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7741 q selected
    | true =>
      simp only [d11060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7742 q selected
  have h3 (q : Pattern) (selected : d11061 q = 1) : d108879 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11061, d108879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d11061, d108879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11067 q = 1) : d11067 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d11068 q = 1) : d108880 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11068, d108880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11068, d108880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11069 q = 1) : d108881 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11069, d108881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11069, d108881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11070 q = 1) : d108882 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11070, d108882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11070, d108882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11071 q = 1) : d108883 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11071, d108883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11071, d108883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7744 (p : Pattern) (selected : d11088 p = 1) : d108889 p = 1 := by
  have h0 (q : Pattern) (selected : d10898 q = 1) : d10898 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d10986 q = 1) : d108867 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10986, d108867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7734 q selected
    | true =>
      simp only [d10986, d108867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7737 q selected
  have h2 (q : Pattern) (selected : d10999 q = 1) : d10999 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d11000 q = 1) : d108868 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11000, d108868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d11000, d108868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d11001 q = 1) : d108869 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11001, d108869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11001, d108869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11002 q = 1) : d108870 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d11002, d108870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11002, d108870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11006 q = 1) : d108874 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11006, d108874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11006, d108874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7738 q selected
  have h8 (q : Pattern) (selected : d11008 q = 1) : d11008 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d11009 q = 1) : d108875 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11009, d108875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11009, d108875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11010 q = 1) : d108876 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11010, d108876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d11010, d108876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d11011 q = 1) : d108877 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d11011, d108877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d11011, d108877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d11012 q = 1) : d108878 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d11012, d108878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11012, d108878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d11072 q = 1) : d108884 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11072, d108884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11072, d108884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7743 q selected
  have h14 (q : Pattern) (selected : d11083 q = 1) : d11083 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d11084 q = 1) : d108885 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11084, d108885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d11084, d108885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d11085 q = 1) : d108886 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d11085, d108886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d11085, d108886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d11086 q = 1) : d108887 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d11086, d108887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d11086, d108887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d11087 q = 1) : d108888 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d11087, d108888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d11087, d108888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d11088 q = 1) : d108889 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d11088, d108889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d11088, d108889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro7745 (p : Pattern) (selected : d11094 p = 1) : d108895 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11089 q = 1) : d108890 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d11089, d108890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11089, d108890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7744 q selected
  have h2 (q : Pattern) (selected : d11090 q = 1) : d108891 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d11090, d108891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11090, d108891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11091 q = 1) : d108892 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d11091, d108892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11091, d108892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11092 q = 1) : d108893 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d11092, d108893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11092, d108893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11093 q = 1) : d108894 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d11093, d108894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11093, d108894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11094 q = 1) : d108895 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d11094, d108895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11094, d108895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7746 (p : Pattern) (selected : d11178 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11169 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro53 q selected
    | true =>
      simp only [d11169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11170 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11171 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11172 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro54 q selected
    | true =>
      simp only [d11172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11173 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11174 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11175 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11176 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11177 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11178 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d11178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro7747 (p : Pattern) (selected : d11182 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11172 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro54 q selected
    | true =>
      simp only [d11172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11173 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11174 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11176 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11181 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11182 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7748 (p : Pattern) (selected : d11188 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11179 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7746 q selected
    | true =>
      simp only [d11179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11180 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11183 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7747 q selected
    | true =>
      simp only [d11183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11184 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11185 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11186 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11187 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11188 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7749 (p : Pattern) (selected : d11192 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d11183 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7747 q selected
    | true =>
      simp only [d11183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11184 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11189 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11190 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11191 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11192 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
end NetHack.Soko22Hazard87
