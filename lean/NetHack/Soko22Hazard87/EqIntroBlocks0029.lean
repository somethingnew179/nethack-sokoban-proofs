import NetHack.Soko22Hazard87.EqIntroBlocks0028
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro7250 (p : Pattern) (selected : d104947 p = 0) : d105790 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104938 q = 0) : d105781 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104938, d105781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7248 q selected
    | true =>
      simp only [d104938, d105781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104939 q = 0) : d105782 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104939, d105782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104939, d105782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104944 q = 0) : d105787 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104944, d105787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104944, d105787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104945 q = 0) : d105788 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104945, d105788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104945, d105788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104946 q = 0) : d105789 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104946, d105789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104946, d105789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104947 q = 0) : d105790 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104947, d105790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104947, d105790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7251 (p : Pattern) (selected : d104949 p = 0) : d105780 p = 1 := by
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
  have h4 (q : Pattern) (selected : d104949 q = 0) : d105780 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d104949, d105780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104949, d105780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7252 (p : Pattern) (selected : d104955 p = 0) : d105790 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104950 q = 0) : d105781 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104950, d105781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7251 q selected
    | true =>
      simp only [d104950, d105781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104951 q = 0) : d105782 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104951, d105782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104951, d105782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104952 q = 0) : d105787 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104952, d105787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104952, d105787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104953 q = 0) : d105788 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104953, d105788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104953, d105788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104954 q = 0) : d105789 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104954, d105789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104954, d105789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104955 q = 0) : d105790 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104955, d105790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104955, d105790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7253 (p : Pattern) (selected : d104963 p = 0) : d105798 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104948 q = 0) : d105791 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104948, d105791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7249 q selected
    | true =>
      simp only [d104948, d105791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7250 q selected
  have h2 (q : Pattern) (selected : d104956 q = 0) : d105792 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104956, d105792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7252 q selected
    | true =>
      simp only [d104956, d105792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d104957 q = 0) : d105793 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104957, d105793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d104957, d105793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d104958 q = 0) : d105792 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104958, d105792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7250 q selected
    | true =>
      simp only [d104958, d105792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104959 q = 0) : d105794 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104959, d105794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104959, d105794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104960 q = 0) : d105795 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104960, d105795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104960, d105795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d104961 q = 0) : d105796 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104961, d105796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104961, d105796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d104962 q = 0) : d105797 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104962, d105797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104962, d105797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d104963 q = 0) : d105798 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104963, d105798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104963, d105798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7254 (p : Pattern) (selected : d104969 p = 0) : d105804 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104855 q = 0) : d105708 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d104855, d105708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104855, d105708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7230 q selected
  have h2 (q : Pattern) (selected : d104856 q = 0) : d105709 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d104856, d105709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d104856, d105709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d104864 q = 0) : d105717 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d104864, d105717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7230 q selected
    | true =>
      simp only [d104864, d105717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7232 q selected
  have h4 (q : Pattern) (selected : d104865 q = 0) : d105718 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d104865, d105718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104865, d105718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104866 q = 0) : d105719 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d104866, d105719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104866, d105719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104920 q = 0) : d105763 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d104920, d105763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7239 q selected
    | true =>
      simp only [d104920, d105763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7244 q selected
  have h7 (q : Pattern) (selected : d104922 q = 0) : d105765 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d104922, d105765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7245 q selected
    | true =>
      simp only [d104922, d105765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d104923 q = 0) : d105766 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d104923, d105766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d104923, d105766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d104924 q = 0) : d105767 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d104924, d105767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d104924, d105767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d104925 q = 0) : d105768 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d104925, d105768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104925, d105768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d104929 q = 0) : d105772 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d104929, d105772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104929, d105772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7246 q selected
  have h12 (q : Pattern) (selected : d104930 q = 0) : d105773 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d104930, d105773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d104930, d105773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d104931 q = 0) : d105774 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d104931, d105774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d104931, d105774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d104932 q = 0) : d105775 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d104932, d105775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d104932, d105775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d104933 q = 0) : d105776 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d104933, d105776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d104933, d105776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d104964 q = 0) : d105799 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d104964, d105799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104964, d105799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7253 q selected
  have h17 (q : Pattern) (selected : d104965 q = 0) : d105800 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d104965, d105800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d104965, d105800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d104966 q = 0) : d105801 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d104966, d105801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d104966, d105801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d104967 q = 0) : d105802 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d104967, d105802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d104967, d105802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d104968 q = 0) : d105803 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d104968, d105803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d104968, d105803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d104969 q = 0) : d105804 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d104969, d105804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d104969, d105804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro7255 (p : Pattern) (selected : d104975 p = 0) : d105810 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104970 q = 0) : d105805 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d104970, d105805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104970, d105805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7254 q selected
  have h2 (q : Pattern) (selected : d104971 q = 0) : d105806 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d104971, d105806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104971, d105806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104972 q = 0) : d105807 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d104972, d105807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104972, d105807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d104973 q = 0) : d105808 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d104973, d105808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104973, d105808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104974 q = 0) : d105809 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d104974, d105809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104974, d105809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104975 q = 0) : d105810 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d104975, d105810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104975, d105810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7256 (p : Pattern) (selected : d104978 p = 0) : d105813 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1142 q = 0) : d52723 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1142, d52723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro390 q selected
    | true =>
      simp only [d1142, d52723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro392 q selected
  have h2 (q : Pattern) (selected : d1143 q = 0) : d52724 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1143, d52724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1143, d52724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1144 q = 0) : d52725 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1144, d52725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1144, d52725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d104978 q = 0) : d105813 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d104978, d105813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104978, d105813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7257 (p : Pattern) (selected : d104984 p = 0) : d105819 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104979 q = 0) : d105814 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104979, d105814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7256 q selected
    | true =>
      simp only [d104979, d105814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104980 q = 0) : d105815 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104980, d105815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104980, d105815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104981 q = 0) : d105816 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104981, d105816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104981, d105816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104982 q = 0) : d105817 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104982, d105817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104982, d105817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104983 q = 0) : d105818 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104983, d105818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104983, d105818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104984 q = 0) : d105819 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104984, d105819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104984, d105819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7258 (p : Pattern) (selected : d104990 p = 0) : d105825 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104985 q = 0) : d105820 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104985, d105820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7257 q selected
    | true =>
      simp only [d104985, d105820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104986 q = 0) : d105821 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104986, d105821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104986, d105821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104987 q = 0) : d105822 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104987, d105822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104987, d105822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104988 q = 0) : d105823 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104988, d105823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104988, d105823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104989 q = 0) : d105824 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104989, d105824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104989, d105824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104990 q = 0) : d105825 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104990, d105825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104990, d105825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7259 (p : Pattern) (selected : d104993 p = 0) : d105828 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104979 q = 0) : d105814 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104979, d105814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7256 q selected
    | true =>
      simp only [d104979, d105814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104980 q = 0) : d105815 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104980, d105815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104980, d105815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104981 q = 0) : d105816 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104981, d105816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104981, d105816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104982 q = 0) : d105817 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104982, d105817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104982, d105817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104983 q = 0) : d105818 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104983, d105818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104983, d105818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104993 q = 0) : d105828 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104993, d105828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104993, d105828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7260 (p : Pattern) (selected : d104999 p = 0) : d105834 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104985 q = 0) : d105820 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104985, d105820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7257 q selected
    | true =>
      simp only [d104985, d105820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104986 q = 0) : d105821 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104986, d105821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104986, d105821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104987 q = 0) : d105822 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104987, d105822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104987, d105822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104988 q = 0) : d105823 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104988, d105823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104988, d105823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104989 q = 0) : d105824 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104989, d105824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104989, d105824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104994 q = 0) : d105829 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104994, d105829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7259 q selected
    | true =>
      simp only [d104994, d105829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d104995 q = 0) : d105830 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104995, d105830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104995, d105830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d104996 q = 0) : d105831 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104996, d105831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d104996, d105831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d104997 q = 0) : d105832 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104997, d105832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104997, d105832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d104998 q = 0) : d105833 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104998, d105833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104998, d105833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d104999 q = 0) : d105834 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104999, d105834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104999, d105834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro7261 (p : Pattern) (selected : d105004 p = 0) : d105839 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104979 q = 0) : d105814 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104979, d105814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7256 q selected
    | true =>
      simp only [d104979, d105814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104980 q = 0) : d105815 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104980, d105815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104980, d105815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104981 q = 0) : d105816 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104981, d105816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104981, d105816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104982 q = 0) : d105817 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104982, d105817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104982, d105817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105003 q = 0) : d105838 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105003, d105838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105003, d105838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105004 q = 0) : d105839 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105004, d105839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105004, d105839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7262 (p : Pattern) (selected : d105011 p = 0) : d105846 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104979 q = 0) : d105814 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104979, d105814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7256 q selected
    | true =>
      simp only [d104979, d105814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104980 q = 0) : d105815 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104980, d105815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104980, d105815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104981 q = 0) : d105816 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104981, d105816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104981, d105816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105009 q = 0) : d105844 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105009, d105844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105009, d105844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d105010 q = 0) : d105845 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105010, d105845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105010, d105845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105011 q = 0) : d105846 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105011, d105846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105011, d105846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7263 (p : Pattern) (selected : d105015 p = 0) : d105850 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1129 q = 0) : d52710 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1129, d52710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro389 q selected
    | true =>
      simp only [d1129, d52710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro390 q selected
  have h2 (q : Pattern) (selected : d1130 q = 0) : d52711 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1130, d52711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1130, d52711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1131 q = 0) : d52712 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1131, d52712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1131, d52712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105015 q = 0) : d105850 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d105015, d105850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105015, d105850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7264 (p : Pattern) (selected : d105021 p = 0) : d105856 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105016 q = 0) : d105851 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105016, d105851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7263 q selected
    | true =>
      simp only [d105016, d105851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105017 q = 0) : d105852 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105017, d105852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105017, d105852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104979 q = 0) : d105814 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104979, d105814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7256 q selected
    | true =>
      simp only [d104979, d105814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104980 q = 0) : d105815 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104980, d105815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104980, d105815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d105018 q = 0) : d105853 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105018, d105853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105018, d105853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105019 q = 0) : d105854 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105019, d105854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105019, d105854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d105020 q = 0) : d105855 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105020, d105855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d105020, d105855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d105021 q = 0) : d105856 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105021, d105856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105021, d105856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7265 (p : Pattern) (selected : d105023 p = 0) : d105813 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1297 q = 0) : d52723 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1297, d52723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro419 q selected
    | true =>
      simp only [d1297, d52723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro421 q selected
  have h2 (q : Pattern) (selected : d1298 q = 0) : d52724 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1298, d52724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1298, d52724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1299 q = 0) : d52725 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1299, d52725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1299, d52725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105023 q = 0) : d105813 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d105023, d105813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105023, d105813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7266 (p : Pattern) (selected : d105029 p = 0) : d105819 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105024 q = 0) : d105814 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105024, d105814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7265 q selected
    | true =>
      simp only [d105024, d105814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105025 q = 0) : d105815 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105025, d105815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105025, d105815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105026 q = 0) : d105816 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105026, d105816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105026, d105816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105027 q = 0) : d105817 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105027, d105817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105027, d105817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105028 q = 0) : d105818 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105028, d105818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105028, d105818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105029 q = 0) : d105819 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105029, d105819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105029, d105819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7267 (p : Pattern) (selected : d105036 p = 0) : d105863 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105005 q = 0) : d105840 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105005, d105840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7261 q selected
    | true =>
      simp only [d105005, d105840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105006 q = 0) : d105841 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105006, d105841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105006, d105841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105007 q = 0) : d105842 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105007, d105842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105007, d105842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105008 q = 0) : d105843 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105008, d105843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105008, d105843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d105012 q = 0) : d105847 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105012, d105847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7262 q selected
    | true =>
      simp only [d105012, d105847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105013 q = 0) : d105848 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105013, d105848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105013, d105848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d105014 q = 0) : d105849 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105014, d105849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d105014, d105849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d105022 q = 0) : d105857 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105022, d105857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7264 q selected
    | true =>
      simp only [d105022, d105857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7257 q selected
  have h9 (q : Pattern) (selected : d105030 q = 0) : d105820 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105030, d105820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7266 q selected
    | true =>
      simp only [d105030, d105820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d105031 q = 0) : d105858 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105031, d105858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d105031, d105858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d104985 q = 0) : d105820 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104985, d105820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7257 q selected
    | true =>
      simp only [d104985, d105820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d105032 q = 0) : d105859 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105032, d105859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d105032, d105859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d105033 q = 0) : d105860 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105033, d105860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d105033, d105860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d105034 q = 0) : d105861 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105034, d105861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d105034, d105861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d105035 q = 0) : d105862 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105035, d105862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105035, d105862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d105036 q = 0) : d105863 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105036, d105863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105036, d105863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro7268 (p : Pattern) (selected : d105037 p = 0) : d105864 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104979 q = 0) : d105814 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104979, d105814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7256 q selected
    | true =>
      simp only [d104979, d105814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104980 q = 0) : d105815 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104980, d105815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104980, d105815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104981 q = 0) : d105816 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104981, d105816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104981, d105816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104982 q = 0) : d105817 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104982, d105817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104982, d105817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105003 q = 0) : d105838 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105003, d105838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105003, d105838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105037 q = 0) : d105864 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105037, d105864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105037, d105864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7269 (p : Pattern) (selected : d105042 p = 0) : d105869 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104979 q = 0) : d105814 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104979, d105814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7256 q selected
    | true =>
      simp only [d104979, d105814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104980 q = 0) : d105815 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104980, d105815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104980, d105815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104981 q = 0) : d105816 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104981, d105816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104981, d105816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105009 q = 0) : d105844 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105009, d105844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105009, d105844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d105010 q = 0) : d105845 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105010, d105845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105010, d105845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105042 q = 0) : d105869 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105042, d105869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105042, d105869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7270 (p : Pattern) (selected : d105046 p = 0) : d105873 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105016 q = 0) : d105851 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105016, d105851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7263 q selected
    | true =>
      simp only [d105016, d105851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105017 q = 0) : d105852 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105017, d105852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105017, d105852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104979 q = 0) : d105814 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104979, d105814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7256 q selected
    | true =>
      simp only [d104979, d105814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104980 q = 0) : d105815 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104980, d105815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104980, d105815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d105018 q = 0) : d105853 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105018, d105853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105018, d105853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105019 q = 0) : d105854 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105019, d105854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105019, d105854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d105020 q = 0) : d105855 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105020, d105855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d105020, d105855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d105046 q = 0) : d105873 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105046, d105873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d105046, d105873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7271 (p : Pattern) (selected : d105048 p = 0) : d105828 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105024 q = 0) : d105814 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105024, d105814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7265 q selected
    | true =>
      simp only [d105024, d105814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105025 q = 0) : d105815 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105025, d105815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105025, d105815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105026 q = 0) : d105816 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105026, d105816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105026, d105816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105027 q = 0) : d105817 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105027, d105817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105027, d105817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105028 q = 0) : d105818 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105028, d105818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105028, d105818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105048 q = 0) : d105828 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105048, d105828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105048, d105828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7272 (p : Pattern) (selected : d105055 p = 0) : d105880 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105005 q = 0) : d105840 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105005, d105840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7261 q selected
    | true =>
      simp only [d105005, d105840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105006 q = 0) : d105841 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105006, d105841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105006, d105841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105007 q = 0) : d105842 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105007, d105842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105007, d105842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105008 q = 0) : d105843 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105008, d105843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105008, d105843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d105012 q = 0) : d105847 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105012, d105847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7262 q selected
    | true =>
      simp only [d105012, d105847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105013 q = 0) : d105848 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105013, d105848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105013, d105848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d105014 q = 0) : d105849 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105014, d105849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d105014, d105849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d105022 q = 0) : d105857 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105022, d105857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7264 q selected
    | true =>
      simp only [d105022, d105857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7257 q selected
  have h9 (q : Pattern) (selected : d105030 q = 0) : d105820 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105030, d105820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7266 q selected
    | true =>
      simp only [d105030, d105820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d105031 q = 0) : d105858 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105031, d105858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d105031, d105858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d104985 q = 0) : d105820 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104985, d105820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7257 q selected
    | true =>
      simp only [d104985, d105820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d105032 q = 0) : d105859 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105032, d105859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d105032, d105859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d105033 q = 0) : d105860 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105033, d105860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d105033, d105860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d105034 q = 0) : d105861 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105034, d105861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d105034, d105861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d105035 q = 0) : d105862 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105035, d105862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105035, d105862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d105038 q = 0) : d105865 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105038, d105865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7268 q selected
    | true =>
      simp only [d105038, d105865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d105039 q = 0) : d105866 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105039, d105866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105039, d105866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d105040 q = 0) : d105867 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105040, d105867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d105040, d105867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d105041 q = 0) : d105868 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105041, d105868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105041, d105868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d105043 q = 0) : d105870 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105043, d105870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7269 q selected
    | true =>
      simp only [d105043, d105870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d105044 q = 0) : d105871 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105044, d105871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105044, d105871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d105045 q = 0) : d105872 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105045, d105872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d105045, d105872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d105047 q = 0) : d105874 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105047, d105874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7270 q selected
    | true =>
      simp only [d105047, d105874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7259 q selected
  have h24 (q : Pattern) (selected : d105049 q = 0) : d105829 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105049, d105829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7271 q selected
    | true =>
      simp only [d105049, d105829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d105050 q = 0) : d105875 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105050, d105875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d105050, d105875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d104994 q = 0) : d105829 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104994, d105829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7259 q selected
    | true =>
      simp only [d104994, d105829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d105051 q = 0) : d105876 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105051, d105876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d105051, d105876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d105052 q = 0) : d105877 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105052, d105877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d105052, d105877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d105053 q = 0) : d105878 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105053, d105878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d105053, d105878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d105054 q = 0) : d105879 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105054, d105879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d105054, d105879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d105055 q = 0) : d105880 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105055, d105880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d105055, d105880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro7273 (p : Pattern) (selected : d105057 p = 0) : d105882 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104985 q = 0) : d105820 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104985, d105820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7257 q selected
    | true =>
      simp only [d104985, d105820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104986 q = 0) : d105821 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104986, d105821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104986, d105821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104987 q = 0) : d105822 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104987, d105822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104987, d105822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104988 q = 0) : d105823 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104988, d105823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104988, d105823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104989 q = 0) : d105824 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104989, d105824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104989, d105824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105057 q = 0) : d105882 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105057, d105882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105057, d105882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7274 (p : Pattern) (selected : d105064 p = 0) : d105889 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105047 q = 0) : d105874 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105047, d105874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7270 q selected
    | true =>
      simp only [d105047, d105874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7259 q selected
  have h2 (q : Pattern) (selected : d105049 q = 0) : d105829 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105049, d105829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7271 q selected
    | true =>
      simp only [d105049, d105829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d105050 q = 0) : d105875 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105050, d105875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105050, d105875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d104994 q = 0) : d105829 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104994, d105829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7259 q selected
    | true =>
      simp only [d104994, d105829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105051 q = 0) : d105876 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105051, d105876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105051, d105876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105052 q = 0) : d105877 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105052, d105877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105052, d105877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d105062 q = 0) : d105887 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105062, d105887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105062, d105887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d105063 q = 0) : d105888 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105063, d105888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105063, d105888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d105064 q = 0) : d105889 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105064, d105889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105064, d105889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7275 (p : Pattern) (selected : d105070 p = 0) : d105895 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1402 q = 0) : d52890 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1402, d52890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro440 q selected
    | true =>
      simp only [d1402, d52890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro441 q selected
  have h2 (q : Pattern) (selected : d1403 q = 0) : d52891 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1403, d52891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1403, d52891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1404 q = 0) : d52892 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1404, d52892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1404, d52892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105070 q = 0) : d105895 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d105070, d105895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105070, d105895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7276 (p : Pattern) (selected : d105073 p = 0) : d105898 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1412 q = 0) : d52900 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1412, d52900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro441 q selected
    | true =>
      simp only [d1412, d52900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro442 q selected
  have h2 (q : Pattern) (selected : d1413 q = 0) : d52901 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1413, d52901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1413, d52901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1414 q = 0) : d52902 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1414, d52902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1414, d52902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105073 q = 0) : d105898 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d105073, d105898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105073, d105898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7277 (p : Pattern) (selected : d105079 p = 0) : d105904 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105071 q = 0) : d105896 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105071, d105896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7275 q selected
    | true =>
      simp only [d105071, d105896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105072 q = 0) : d105897 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105072, d105897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105072, d105897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105074 q = 0) : d105899 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105074, d105899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7276 q selected
    | true =>
      simp only [d105074, d105899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105075 q = 0) : d105900 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105075, d105900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105075, d105900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d105076 q = 0) : d105901 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105076, d105901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105076, d105901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105077 q = 0) : d105902 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105077, d105902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105077, d105902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d105078 q = 0) : d105903 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105078, d105903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d105078, d105903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d105079 q = 0) : d105904 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105079, d105904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d105079, d105904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7278 (p : Pattern) (selected : d105083 p = 0) : d105908 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105074 q = 0) : d105899 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105074, d105899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7276 q selected
    | true =>
      simp only [d105074, d105899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105075 q = 0) : d105900 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105075, d105900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105075, d105900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105080 q = 0) : d105905 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105080, d105905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105080, d105905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105081 q = 0) : d105906 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105081, d105906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105081, d105906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105082 q = 0) : d105907 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105082, d105907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105082, d105907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105083 q = 0) : d105908 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105083, d105908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105083, d105908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7279 (p : Pattern) (selected : d105085 p = 0) : d105898 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1464 q = 0) : d52900 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1464, d52900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro449 q selected
    | true =>
      simp only [d1464, d52900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro450 q selected
  have h2 (q : Pattern) (selected : d1465 q = 0) : d52901 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1465, d52901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1465, d52901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1466 q = 0) : d52902 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1466, d52902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1466, d52902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105085 q = 0) : d105898 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d105085, d105898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105085, d105898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7280 (p : Pattern) (selected : d105091 p = 0) : d105908 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105086 q = 0) : d105899 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105086, d105899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7279 q selected
    | true =>
      simp only [d105086, d105899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105087 q = 0) : d105900 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105087, d105900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105087, d105900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105088 q = 0) : d105905 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105088, d105905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105088, d105905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105089 q = 0) : d105906 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105089, d105906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105089, d105906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105090 q = 0) : d105907 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105090, d105907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105090, d105907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105091 q = 0) : d105908 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105091, d105908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105091, d105908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7281 (p : Pattern) (selected : d105099 p = 0) : d105916 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105084 q = 0) : d105909 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105084, d105909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7277 q selected
    | true =>
      simp only [d105084, d105909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7278 q selected
  have h2 (q : Pattern) (selected : d105092 q = 0) : d105910 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105092, d105910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7280 q selected
    | true =>
      simp only [d105092, d105910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d105093 q = 0) : d105911 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105093, d105911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105093, d105911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105094 q = 0) : d105910 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105094, d105910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7278 q selected
    | true =>
      simp only [d105094, d105910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105095 q = 0) : d105912 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105095, d105912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105095, d105912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105096 q = 0) : d105913 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105096, d105913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105096, d105913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d105097 q = 0) : d105914 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105097, d105914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105097, d105914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d105098 q = 0) : d105915 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105098, d105915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105098, d105915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d105099 q = 0) : d105916 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105099, d105916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105099, d105916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7282 (p : Pattern) (selected : d105105 p = 0) : d105922 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d104991 q = 0) : d105826 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d104991, d105826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104991, d105826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7258 q selected
  have h2 (q : Pattern) (selected : d104992 q = 0) : d105827 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d104992, d105827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d104992, d105827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d105000 q = 0) : d105835 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105000, d105835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7258 q selected
    | true =>
      simp only [d105000, d105835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7260 q selected
  have h4 (q : Pattern) (selected : d105001 q = 0) : d105836 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105001, d105836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105001, d105836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105002 q = 0) : d105837 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d105002, d105837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105002, d105837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105056 q = 0) : d105881 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105056, d105881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7267 q selected
    | true =>
      simp only [d105056, d105881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7272 q selected
  have h7 (q : Pattern) (selected : d105058 q = 0) : d105883 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105058, d105883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7273 q selected
    | true =>
      simp only [d105058, d105883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d105059 q = 0) : d105884 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105059, d105884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d105059, d105884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d105060 q = 0) : d105885 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d105060, d105885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d105060, d105885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d105061 q = 0) : d105886 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d105061, d105886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105061, d105886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d105065 q = 0) : d105890 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105065, d105890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105065, d105890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7274 q selected
  have h12 (q : Pattern) (selected : d105066 q = 0) : d105891 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105066, d105891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d105066, d105891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d105067 q = 0) : d105892 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d105067, d105892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d105067, d105892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d105068 q = 0) : d105893 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d105068, d105893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d105068, d105893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d105069 q = 0) : d105894 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d105069, d105894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d105069, d105894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d105100 q = 0) : d105917 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105100, d105917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105100, d105917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7281 q selected
  have h17 (q : Pattern) (selected : d105101 q = 0) : d105918 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105101, d105918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d105101, d105918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d105102 q = 0) : d105919 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d105102, d105919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d105102, d105919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d105103 q = 0) : d105920 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d105103, d105920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d105103, d105920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d105104 q = 0) : d105921 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d105104, d105921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d105104, d105921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d105105 q = 0) : d105922 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d105105, d105922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d105105, d105922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro7283 (p : Pattern) (selected : d105111 p = 0) : d105928 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105106 q = 0) : d105923 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d105106, d105923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105106, d105923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7282 q selected
  have h2 (q : Pattern) (selected : d105107 q = 0) : d105924 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d105107, d105924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105107, d105924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105108 q = 0) : d105925 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d105108, d105925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105108, d105925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105109 q = 0) : d105926 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d105109, d105926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105109, d105926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d105110 q = 0) : d105927 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d105110, d105927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105110, d105927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105111 q = 0) : d105928 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d105111, d105928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105111, d105928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7284 (p : Pattern) (selected : d105115 p = 0) : d105932 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1603 q = 0) : d53044 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1603, d53044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro472 q selected
    | true =>
      simp only [d1603, d53044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro474 q selected
  have h2 (q : Pattern) (selected : d1604 q = 0) : d53045 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1604, d53045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1604, d53045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1605 q = 0) : d53046 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1605, d53046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1605, d53046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105115 q = 0) : d105932 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d105115, d105932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105115, d105932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7285 (p : Pattern) (selected : d105121 p = 0) : d105938 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105116 q = 0) : d105933 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105116, d105933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7284 q selected
    | true =>
      simp only [d105116, d105933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105117 q = 0) : d105934 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105117, d105934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105117, d105934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105118 q = 0) : d105935 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105118, d105935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105118, d105935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105119 q = 0) : d105936 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105119, d105936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105119, d105936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105120 q = 0) : d105937 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105120, d105937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105120, d105937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105121 q = 0) : d105938 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105121, d105938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105121, d105938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7286 (p : Pattern) (selected : d105127 p = 0) : d105944 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105122 q = 0) : d105939 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105122, d105939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7285 q selected
    | true =>
      simp only [d105122, d105939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105123 q = 0) : d105940 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105123, d105940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105123, d105940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105124 q = 0) : d105941 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105124, d105941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105124, d105941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105125 q = 0) : d105942 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105125, d105942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105125, d105942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d105126 q = 0) : d105943 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105126, d105943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105126, d105943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105127 q = 0) : d105944 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105127, d105944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105127, d105944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7287 (p : Pattern) (selected : d105130 p = 0) : d105947 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105116 q = 0) : d105933 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105116, d105933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7284 q selected
    | true =>
      simp only [d105116, d105933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105117 q = 0) : d105934 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105117, d105934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105117, d105934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105118 q = 0) : d105935 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105118, d105935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105118, d105935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105119 q = 0) : d105936 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105119, d105936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105119, d105936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105120 q = 0) : d105937 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105120, d105937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105120, d105937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105130 q = 0) : d105947 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105130, d105947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105130, d105947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7288 (p : Pattern) (selected : d105136 p = 0) : d105953 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105122 q = 0) : d105939 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105122, d105939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7285 q selected
    | true =>
      simp only [d105122, d105939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105123 q = 0) : d105940 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105123, d105940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105123, d105940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105124 q = 0) : d105941 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105124, d105941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105124, d105941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105125 q = 0) : d105942 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105125, d105942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105125, d105942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d105126 q = 0) : d105943 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105126, d105943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105126, d105943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105131 q = 0) : d105948 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105131, d105948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7287 q selected
    | true =>
      simp only [d105131, d105948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d105132 q = 0) : d105949 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105132, d105949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105132, d105949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d105133 q = 0) : d105950 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105133, d105950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d105133, d105950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d105134 q = 0) : d105951 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105134, d105951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105134, d105951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d105135 q = 0) : d105952 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105135, d105952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105135, d105952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d105136 q = 0) : d105953 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105136, d105953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105136, d105953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro7289 (p : Pattern) (selected : d105141 p = 0) : d105958 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105116 q = 0) : d105933 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105116, d105933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7284 q selected
    | true =>
      simp only [d105116, d105933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105117 q = 0) : d105934 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105117, d105934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105117, d105934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105118 q = 0) : d105935 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105118, d105935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105118, d105935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105119 q = 0) : d105936 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105119, d105936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105119, d105936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105140 q = 0) : d105957 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105140, d105957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105140, d105957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105141 q = 0) : d105958 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105141, d105958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105141, d105958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7290 (p : Pattern) (selected : d105148 p = 0) : d105965 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105116 q = 0) : d105933 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105116, d105933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7284 q selected
    | true =>
      simp only [d105116, d105933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105117 q = 0) : d105934 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105117, d105934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105117, d105934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105118 q = 0) : d105935 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105118, d105935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105118, d105935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105146 q = 0) : d105963 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105146, d105963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105146, d105963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d105147 q = 0) : d105964 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105147, d105964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105147, d105964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105148 q = 0) : d105965 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105148, d105965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105148, d105965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7291 (p : Pattern) (selected : d105152 p = 0) : d105969 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1590 q = 0) : d53031 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1590, d53031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro471 q selected
    | true =>
      simp only [d1590, d53031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro472 q selected
  have h2 (q : Pattern) (selected : d1591 q = 0) : d53032 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1591, d53032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1591, d53032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1592 q = 0) : d53033 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1592, d53033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1592, d53033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105152 q = 0) : d105969 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d105152, d105969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105152, d105969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7292 (p : Pattern) (selected : d105158 p = 0) : d105975 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105153 q = 0) : d105970 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105153, d105970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7291 q selected
    | true =>
      simp only [d105153, d105970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105154 q = 0) : d105971 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105154, d105971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105154, d105971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105116 q = 0) : d105933 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105116, d105933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7284 q selected
    | true =>
      simp only [d105116, d105933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105117 q = 0) : d105934 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105117, d105934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105117, d105934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d105155 q = 0) : d105972 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105155, d105972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105155, d105972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105156 q = 0) : d105973 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105156, d105973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105156, d105973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d105157 q = 0) : d105974 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105157, d105974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d105157, d105974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d105158 q = 0) : d105975 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105158, d105975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105158, d105975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7293 (p : Pattern) (selected : d105160 p = 0) : d105932 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1774 q = 0) : d53044 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1774, d53044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro505 q selected
    | true =>
      simp only [d1774, d53044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro507 q selected
  have h2 (q : Pattern) (selected : d1775 q = 0) : d53045 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1775, d53045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1775, d53045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1776 q = 0) : d53046 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1776, d53046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1776, d53046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105160 q = 0) : d105932 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d105160, d105932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105160, d105932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7294 (p : Pattern) (selected : d105166 p = 0) : d105938 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105161 q = 0) : d105933 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105161, d105933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7293 q selected
    | true =>
      simp only [d105161, d105933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105162 q = 0) : d105934 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105162, d105934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105162, d105934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105163 q = 0) : d105935 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105163, d105935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105163, d105935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105164 q = 0) : d105936 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105164, d105936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105164, d105936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105165 q = 0) : d105937 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105165, d105937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105165, d105937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105166 q = 0) : d105938 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105166, d105938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105166, d105938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7295 (p : Pattern) (selected : d105173 p = 0) : d105982 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105142 q = 0) : d105959 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105142, d105959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7289 q selected
    | true =>
      simp only [d105142, d105959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105143 q = 0) : d105960 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105143, d105960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105143, d105960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105144 q = 0) : d105961 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105144, d105961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105144, d105961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105145 q = 0) : d105962 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105145, d105962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105145, d105962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d105149 q = 0) : d105966 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105149, d105966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7290 q selected
    | true =>
      simp only [d105149, d105966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105150 q = 0) : d105967 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105150, d105967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105150, d105967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d105151 q = 0) : d105968 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105151, d105968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d105151, d105968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d105159 q = 0) : d105976 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105159, d105976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7292 q selected
    | true =>
      simp only [d105159, d105976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7285 q selected
  have h9 (q : Pattern) (selected : d105167 q = 0) : d105939 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105167, d105939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7294 q selected
    | true =>
      simp only [d105167, d105939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d105168 q = 0) : d105977 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105168, d105977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d105168, d105977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d105122 q = 0) : d105939 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105122, d105939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7285 q selected
    | true =>
      simp only [d105122, d105939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d105169 q = 0) : d105978 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105169, d105978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d105169, d105978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d105170 q = 0) : d105979 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105170, d105979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d105170, d105979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d105171 q = 0) : d105980 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105171, d105980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d105171, d105980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d105172 q = 0) : d105981 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105172, d105981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105172, d105981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d105173 q = 0) : d105982 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105173, d105982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105173, d105982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro7296 (p : Pattern) (selected : d105174 p = 0) : d105983 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105116 q = 0) : d105933 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105116, d105933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7284 q selected
    | true =>
      simp only [d105116, d105933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105117 q = 0) : d105934 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105117, d105934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105117, d105934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105118 q = 0) : d105935 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105118, d105935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105118, d105935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105119 q = 0) : d105936 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105119, d105936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105119, d105936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105140 q = 0) : d105957 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105140, d105957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105140, d105957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105174 q = 0) : d105983 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105174, d105983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105174, d105983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7297 (p : Pattern) (selected : d105179 p = 0) : d105988 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105116 q = 0) : d105933 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105116, d105933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7284 q selected
    | true =>
      simp only [d105116, d105933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105117 q = 0) : d105934 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105117, d105934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105117, d105934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105118 q = 0) : d105935 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105118, d105935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105118, d105935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105146 q = 0) : d105963 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105146, d105963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105146, d105963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d105147 q = 0) : d105964 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105147, d105964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105147, d105964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105179 q = 0) : d105988 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105179, d105988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105179, d105988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7298 (p : Pattern) (selected : d105183 p = 0) : d105992 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105153 q = 0) : d105970 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105153, d105970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7291 q selected
    | true =>
      simp only [d105153, d105970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105154 q = 0) : d105971 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105154, d105971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105154, d105971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105116 q = 0) : d105933 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105116, d105933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7284 q selected
    | true =>
      simp only [d105116, d105933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105117 q = 0) : d105934 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105117, d105934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105117, d105934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d105155 q = 0) : d105972 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105155, d105972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105155, d105972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105156 q = 0) : d105973 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105156, d105973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105156, d105973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d105157 q = 0) : d105974 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105157, d105974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d105157, d105974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d105183 q = 0) : d105992 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105183, d105992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d105183, d105992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7299 (p : Pattern) (selected : d105185 p = 0) : d105947 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105161 q = 0) : d105933 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105161, d105933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7293 q selected
    | true =>
      simp only [d105161, d105933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105162 q = 0) : d105934 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105162, d105934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105162, d105934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105163 q = 0) : d105935 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105163, d105935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105163, d105935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105164 q = 0) : d105936 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105164, d105936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105164, d105936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105165 q = 0) : d105937 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105165, d105937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105165, d105937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105185 q = 0) : d105947 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105185, d105947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105185, d105947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7300 (p : Pattern) (selected : d105192 p = 0) : d105999 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105142 q = 0) : d105959 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105142, d105959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7289 q selected
    | true =>
      simp only [d105142, d105959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105143 q = 0) : d105960 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105143, d105960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105143, d105960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105144 q = 0) : d105961 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105144, d105961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105144, d105961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105145 q = 0) : d105962 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105145, d105962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105145, d105962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d105149 q = 0) : d105966 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105149, d105966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7290 q selected
    | true =>
      simp only [d105149, d105966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105150 q = 0) : d105967 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105150, d105967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105150, d105967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d105151 q = 0) : d105968 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105151, d105968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d105151, d105968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d105159 q = 0) : d105976 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105159, d105976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7292 q selected
    | true =>
      simp only [d105159, d105976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7285 q selected
  have h9 (q : Pattern) (selected : d105167 q = 0) : d105939 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105167, d105939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7294 q selected
    | true =>
      simp only [d105167, d105939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d105168 q = 0) : d105977 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105168, d105977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d105168, d105977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d105122 q = 0) : d105939 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105122, d105939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7285 q selected
    | true =>
      simp only [d105122, d105939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d105169 q = 0) : d105978 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105169, d105978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d105169, d105978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d105170 q = 0) : d105979 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105170, d105979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d105170, d105979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d105171 q = 0) : d105980 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105171, d105980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d105171, d105980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d105172 q = 0) : d105981 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105172, d105981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105172, d105981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d105175 q = 0) : d105984 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105175, d105984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7296 q selected
    | true =>
      simp only [d105175, d105984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d105176 q = 0) : d105985 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105176, d105985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105176, d105985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d105177 q = 0) : d105986 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105177, d105986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d105177, d105986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d105178 q = 0) : d105987 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105178, d105987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105178, d105987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d105180 q = 0) : d105989 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105180, d105989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7297 q selected
    | true =>
      simp only [d105180, d105989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d105181 q = 0) : d105990 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105181, d105990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105181, d105990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d105182 q = 0) : d105991 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105182, d105991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d105182, d105991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d105184 q = 0) : d105993 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105184, d105993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7298 q selected
    | true =>
      simp only [d105184, d105993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7287 q selected
  have h24 (q : Pattern) (selected : d105186 q = 0) : d105948 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105186, d105948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7299 q selected
    | true =>
      simp only [d105186, d105948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d105187 q = 0) : d105994 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105187, d105994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d105187, d105994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d105131 q = 0) : d105948 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105131, d105948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7287 q selected
    | true =>
      simp only [d105131, d105948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d105188 q = 0) : d105995 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105188, d105995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d105188, d105995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d105189 q = 0) : d105996 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105189, d105996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d105189, d105996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d105190 q = 0) : d105997 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105190, d105997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d105190, d105997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d105191 q = 0) : d105998 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105191, d105998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d105191, d105998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d105192 q = 0) : d105999 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105192, d105999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d105192, d105999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro7301 (p : Pattern) (selected : d105194 p = 0) : d106001 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105122 q = 0) : d105939 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105122, d105939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7285 q selected
    | true =>
      simp only [d105122, d105939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105123 q = 0) : d105940 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105123, d105940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105123, d105940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105124 q = 0) : d105941 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105124, d105941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105124, d105941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105125 q = 0) : d105942 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105125, d105942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105125, d105942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d105126 q = 0) : d105943 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105126, d105943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105126, d105943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105194 q = 0) : d106001 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105194, d106001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105194, d106001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7302 (p : Pattern) (selected : d105201 p = 0) : d106008 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105184 q = 0) : d105993 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105184, d105993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7298 q selected
    | true =>
      simp only [d105184, d105993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7287 q selected
  have h2 (q : Pattern) (selected : d105186 q = 0) : d105948 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105186, d105948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7299 q selected
    | true =>
      simp only [d105186, d105948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d105187 q = 0) : d105994 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105187, d105994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105187, d105994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105131 q = 0) : d105948 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105131, d105948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7287 q selected
    | true =>
      simp only [d105131, d105948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105188 q = 0) : d105995 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105188, d105995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105188, d105995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105189 q = 0) : d105996 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105189, d105996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105189, d105996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d105199 q = 0) : d106006 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105199, d106006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105199, d106006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d105200 q = 0) : d106007 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105200, d106007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105200, d106007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d105201 q = 0) : d106008 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105201, d106008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105201, d106008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7303 (p : Pattern) (selected : d105207 p = 0) : d106014 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1879 q = 0) : d53205 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, d53205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro526 q selected
    | true =>
      simp only [d1879, d53205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro527 q selected
  have h2 (q : Pattern) (selected : d1880 q = 0) : d53206 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, d53206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1880, d53206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1881 q = 0) : d53207 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, d53207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1881, d53207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105207 q = 0) : d106014 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d105207, d106014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105207, d106014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7304 (p : Pattern) (selected : d105210 p = 0) : d106017 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1889 q = 0) : d53215 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1889, d53215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro527 q selected
    | true =>
      simp only [d1889, d53215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro528 q selected
  have h2 (q : Pattern) (selected : d1890 q = 0) : d53216 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1890, d53216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1890, d53216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1891 q = 0) : d53217 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1891, d53217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1891, d53217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105210 q = 0) : d106017 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d105210, d106017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105210, d106017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7305 (p : Pattern) (selected : d105216 p = 0) : d106023 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105208 q = 0) : d106015 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105208, d106015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7303 q selected
    | true =>
      simp only [d105208, d106015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105209 q = 0) : d106016 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105209, d106016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105209, d106016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105211 q = 0) : d106018 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105211, d106018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7304 q selected
    | true =>
      simp only [d105211, d106018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105212 q = 0) : d106019 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105212, d106019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105212, d106019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d105213 q = 0) : d106020 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105213, d106020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105213, d106020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105214 q = 0) : d106021 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105214, d106021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105214, d106021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d105215 q = 0) : d106022 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105215, d106022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d105215, d106022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d105216 q = 0) : d106023 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105216, d106023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d105216, d106023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7306 (p : Pattern) (selected : d105220 p = 0) : d106027 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105211 q = 0) : d106018 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105211, d106018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7304 q selected
    | true =>
      simp only [d105211, d106018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105212 q = 0) : d106019 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105212, d106019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105212, d106019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105217 q = 0) : d106024 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105217, d106024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105217, d106024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105218 q = 0) : d106025 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105218, d106025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105218, d106025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105219 q = 0) : d106026 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105219, d106026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105219, d106026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105220 q = 0) : d106027 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105220, d106027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105220, d106027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7307 (p : Pattern) (selected : d105222 p = 0) : d106017 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1941 q = 0) : d53215 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1941, d53215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro535 q selected
    | true =>
      simp only [d1941, d53215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro536 q selected
  have h2 (q : Pattern) (selected : d1942 q = 0) : d53216 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1942, d53216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1942, d53216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1943 q = 0) : d53217 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1943, d53217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1943, d53217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105222 q = 0) : d106017 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d105222, d106017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105222, d106017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7308 (p : Pattern) (selected : d105228 p = 0) : d106027 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105223 q = 0) : d106018 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105223, d106018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7307 q selected
    | true =>
      simp only [d105223, d106018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105224 q = 0) : d106019 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105224, d106019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105224, d106019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105225 q = 0) : d106024 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105225, d106024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105225, d106024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105226 q = 0) : d106025 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105226, d106025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105226, d106025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105227 q = 0) : d106026 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105227, d106026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105227, d106026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105228 q = 0) : d106027 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105228, d106027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105228, d106027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7309 (p : Pattern) (selected : d105236 p = 0) : d106035 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105221 q = 0) : d106028 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105221, d106028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7305 q selected
    | true =>
      simp only [d105221, d106028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7306 q selected
  have h2 (q : Pattern) (selected : d105229 q = 0) : d106029 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105229, d106029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7308 q selected
    | true =>
      simp only [d105229, d106029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d105230 q = 0) : d106030 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105230, d106030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105230, d106030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105231 q = 0) : d106029 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105231, d106029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7306 q selected
    | true =>
      simp only [d105231, d106029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105232 q = 0) : d106031 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105232, d106031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105232, d106031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105233 q = 0) : d106032 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105233, d106032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105233, d106032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d105234 q = 0) : d106033 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105234, d106033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105234, d106033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d105235 q = 0) : d106034 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105235, d106034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105235, d106034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d105236 q = 0) : d106035 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105236, d106035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105236, d106035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7310 (p : Pattern) (selected : d105242 p = 0) : d106041 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105128 q = 0) : d105945 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105128, d105945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105128, d105945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7286 q selected
  have h2 (q : Pattern) (selected : d105129 q = 0) : d105946 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105129, d105946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105129, d105946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d105137 q = 0) : d105954 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105137, d105954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7286 q selected
    | true =>
      simp only [d105137, d105954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7288 q selected
  have h4 (q : Pattern) (selected : d105138 q = 0) : d105955 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105138, d105955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105138, d105955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105139 q = 0) : d105956 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d105139, d105956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105139, d105956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105193 q = 0) : d106000 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105193, d106000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7295 q selected
    | true =>
      simp only [d105193, d106000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7300 q selected
  have h7 (q : Pattern) (selected : d105195 q = 0) : d106002 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105195, d106002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7301 q selected
    | true =>
      simp only [d105195, d106002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d105196 q = 0) : d106003 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105196, d106003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d105196, d106003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d105197 q = 0) : d106004 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d105197, d106004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d105197, d106004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d105198 q = 0) : d106005 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d105198, d106005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105198, d106005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d105202 q = 0) : d106009 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105202, d106009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105202, d106009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7302 q selected
  have h12 (q : Pattern) (selected : d105203 q = 0) : d106010 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105203, d106010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d105203, d106010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d105204 q = 0) : d106011 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d105204, d106011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d105204, d106011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d105205 q = 0) : d106012 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d105205, d106012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d105205, d106012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d105206 q = 0) : d106013 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d105206, d106013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d105206, d106013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d105237 q = 0) : d106036 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105237, d106036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105237, d106036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7309 q selected
  have h17 (q : Pattern) (selected : d105238 q = 0) : d106037 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105238, d106037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d105238, d106037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d105239 q = 0) : d106038 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d105239, d106038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d105239, d106038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d105240 q = 0) : d106039 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d105240, d106039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d105240, d106039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d105241 q = 0) : d106040 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d105241, d106040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d105241, d106040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d105242 q = 0) : d106041 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d105242, d106041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d105242, d106041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro7311 (p : Pattern) (selected : d105248 p = 0) : d106047 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105243 q = 0) : d106042 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d105243, d106042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105243, d106042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7310 q selected
  have h2 (q : Pattern) (selected : d105244 q = 0) : d106043 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d105244, d106043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105244, d106043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105245 q = 0) : d106044 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d105245, d106044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105245, d106044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105246 q = 0) : d106045 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d105246, d106045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105246, d106045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d105247 q = 0) : d106046 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d105247, d106046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105247, d106046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105248 q = 0) : d106047 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d105248, d106047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105248, d106047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7312 (p : Pattern) (selected : d105253 p = 0) : d106052 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2086 q = 0) : d53365 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2086, d53365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro561 q selected
    | true =>
      simp only [d2086, d53365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro563 q selected
  have h2 (q : Pattern) (selected : d2087 q = 0) : d53366 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2087, d53366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2087, d53366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2088 q = 0) : d53367 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2088, d53367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2088, d53367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105253 q = 0) : d106052 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d105253, d106052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105253, d106052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7313 (p : Pattern) (selected : d105259 p = 0) : d106058 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105254 q = 0) : d106053 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105254, d106053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7312 q selected
    | true =>
      simp only [d105254, d106053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105255 q = 0) : d106054 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105255, d106054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105255, d106054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105256 q = 0) : d106055 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105256, d106055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105256, d106055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105257 q = 0) : d106056 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105257, d106056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105257, d106056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105258 q = 0) : d106057 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105258, d106057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105258, d106057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105259 q = 0) : d106058 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105259, d106058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105259, d106058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7314 (p : Pattern) (selected : d105265 p = 0) : d106064 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105260 q = 0) : d106059 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105260, d106059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7313 q selected
    | true =>
      simp only [d105260, d106059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105261 q = 0) : d106060 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105261, d106060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105261, d106060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105262 q = 0) : d106061 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105262, d106061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105262, d106061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105263 q = 0) : d106062 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105263, d106062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105263, d106062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d105264 q = 0) : d106063 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105264, d106063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105264, d106063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105265 q = 0) : d106064 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105265, d106064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105265, d106064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7315 (p : Pattern) (selected : d105268 p = 0) : d106067 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105254 q = 0) : d106053 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105254, d106053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7312 q selected
    | true =>
      simp only [d105254, d106053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105255 q = 0) : d106054 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105255, d106054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105255, d106054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105256 q = 0) : d106055 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105256, d106055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105256, d106055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105257 q = 0) : d106056 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105257, d106056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105257, d106056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105258 q = 0) : d106057 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105258, d106057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105258, d106057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105268 q = 0) : d106067 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105268, d106067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105268, d106067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7316 (p : Pattern) (selected : d105274 p = 0) : d106073 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105260 q = 0) : d106059 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105260, d106059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7313 q selected
    | true =>
      simp only [d105260, d106059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105261 q = 0) : d106060 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105261, d106060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105261, d106060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105262 q = 0) : d106061 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105262, d106061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105262, d106061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105263 q = 0) : d106062 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105263, d106062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105263, d106062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d105264 q = 0) : d106063 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105264, d106063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105264, d106063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105269 q = 0) : d106068 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105269, d106068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7315 q selected
    | true =>
      simp only [d105269, d106068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d105270 q = 0) : d106069 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105270, d106069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105270, d106069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d105271 q = 0) : d106070 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105271, d106070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d105271, d106070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d105272 q = 0) : d106071 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105272, d106071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105272, d106071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d105273 q = 0) : d106072 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105273, d106072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105273, d106072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d105274 q = 0) : d106073 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105274, d106073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105274, d106073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro7317 (p : Pattern) (selected : d105279 p = 0) : d106078 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105254 q = 0) : d106053 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105254, d106053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7312 q selected
    | true =>
      simp only [d105254, d106053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105255 q = 0) : d106054 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105255, d106054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105255, d106054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105256 q = 0) : d106055 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105256, d106055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105256, d106055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105257 q = 0) : d106056 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105257, d106056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105257, d106056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105278 q = 0) : d106077 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105278, d106077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105278, d106077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105279 q = 0) : d106078 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105279, d106078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105279, d106078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7318 (p : Pattern) (selected : d105286 p = 0) : d106085 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105254 q = 0) : d106053 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105254, d106053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7312 q selected
    | true =>
      simp only [d105254, d106053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105255 q = 0) : d106054 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105255, d106054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105255, d106054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105256 q = 0) : d106055 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105256, d106055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105256, d106055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105284 q = 0) : d106083 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105284, d106083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105284, d106083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d105285 q = 0) : d106084 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105285, d106084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105285, d106084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105286 q = 0) : d106085 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105286, d106085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105286, d106085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7319 (p : Pattern) (selected : d105290 p = 0) : d106089 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2073 q = 0) : d53352 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2073, d53352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro560 q selected
    | true =>
      simp only [d2073, d53352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro561 q selected
  have h2 (q : Pattern) (selected : d2074 q = 0) : d53353 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2074, d53353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2074, d53353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2075 q = 0) : d53354 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2075, d53354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2075, d53354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105290 q = 0) : d106089 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d105290, d106089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105290, d106089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7320 (p : Pattern) (selected : d105296 p = 0) : d106095 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105291 q = 0) : d106090 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105291, d106090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7319 q selected
    | true =>
      simp only [d105291, d106090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105292 q = 0) : d106091 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105292, d106091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105292, d106091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105254 q = 0) : d106053 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105254, d106053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7312 q selected
    | true =>
      simp only [d105254, d106053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105255 q = 0) : d106054 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105255, d106054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105255, d106054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d105293 q = 0) : d106092 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105293, d106092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105293, d106092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105294 q = 0) : d106093 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105294, d106093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105294, d106093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d105295 q = 0) : d106094 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105295, d106094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d105295, d106094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d105296 q = 0) : d106095 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105296, d106095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105296, d106095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7321 (p : Pattern) (selected : d105298 p = 0) : d106052 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2252 q = 0) : d53365 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2252, d53365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro595 q selected
    | true =>
      simp only [d2252, d53365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro597 q selected
  have h2 (q : Pattern) (selected : d2253 q = 0) : d53366 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2253, d53366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2253, d53366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2254 q = 0) : d53367 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2254, d53367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2254, d53367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105298 q = 0) : d106052 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d105298, d106052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105298, d106052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7322 (p : Pattern) (selected : d105304 p = 0) : d106058 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105299 q = 0) : d106053 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105299, d106053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7321 q selected
    | true =>
      simp only [d105299, d106053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105300 q = 0) : d106054 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105300, d106054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105300, d106054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105301 q = 0) : d106055 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105301, d106055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105301, d106055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105302 q = 0) : d106056 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105302, d106056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105302, d106056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105303 q = 0) : d106057 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105303, d106057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105303, d106057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105304 q = 0) : d106058 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105304, d106058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105304, d106058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7323 (p : Pattern) (selected : d105311 p = 0) : d106102 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105280 q = 0) : d106079 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105280, d106079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7317 q selected
    | true =>
      simp only [d105280, d106079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105281 q = 0) : d106080 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105281, d106080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105281, d106080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105282 q = 0) : d106081 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105282, d106081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105282, d106081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105283 q = 0) : d106082 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105283, d106082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105283, d106082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d105287 q = 0) : d106086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105287, d106086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7318 q selected
    | true =>
      simp only [d105287, d106086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105288 q = 0) : d106087 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105288, d106087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105288, d106087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d105289 q = 0) : d106088 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105289, d106088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d105289, d106088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d105297 q = 0) : d106096 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105297, d106096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7320 q selected
    | true =>
      simp only [d105297, d106096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7313 q selected
  have h9 (q : Pattern) (selected : d105305 q = 0) : d106059 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105305, d106059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7322 q selected
    | true =>
      simp only [d105305, d106059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d105306 q = 0) : d106097 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105306, d106097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d105306, d106097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d105260 q = 0) : d106059 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105260, d106059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7313 q selected
    | true =>
      simp only [d105260, d106059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d105307 q = 0) : d106098 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105307, d106098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d105307, d106098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d105308 q = 0) : d106099 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105308, d106099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d105308, d106099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d105309 q = 0) : d106100 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105309, d106100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d105309, d106100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d105310 q = 0) : d106101 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105310, d106101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105310, d106101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d105311 q = 0) : d106102 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105311, d106102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105311, d106102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro7324 (p : Pattern) (selected : d105312 p = 0) : d106103 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105254 q = 0) : d106053 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105254, d106053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7312 q selected
    | true =>
      simp only [d105254, d106053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105255 q = 0) : d106054 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105255, d106054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105255, d106054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105256 q = 0) : d106055 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105256, d106055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105256, d106055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105257 q = 0) : d106056 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105257, d106056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105257, d106056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105278 q = 0) : d106077 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105278, d106077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105278, d106077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105312 q = 0) : d106103 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105312, d106103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105312, d106103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7325 (p : Pattern) (selected : d105317 p = 0) : d106108 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105254 q = 0) : d106053 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105254, d106053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7312 q selected
    | true =>
      simp only [d105254, d106053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105255 q = 0) : d106054 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105255, d106054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105255, d106054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105256 q = 0) : d106055 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105256, d106055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105256, d106055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105284 q = 0) : d106083 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105284, d106083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105284, d106083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d105285 q = 0) : d106084 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105285, d106084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105285, d106084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105317 q = 0) : d106108 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105317, d106108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105317, d106108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7326 (p : Pattern) (selected : d105321 p = 0) : d106112 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105291 q = 0) : d106090 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105291, d106090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7319 q selected
    | true =>
      simp only [d105291, d106090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105292 q = 0) : d106091 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105292, d106091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105292, d106091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105254 q = 0) : d106053 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105254, d106053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7312 q selected
    | true =>
      simp only [d105254, d106053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105255 q = 0) : d106054 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105255, d106054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105255, d106054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d105293 q = 0) : d106092 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105293, d106092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105293, d106092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105294 q = 0) : d106093 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105294, d106093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105294, d106093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d105295 q = 0) : d106094 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105295, d106094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d105295, d106094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d105321 q = 0) : d106112 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105321, d106112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d105321, d106112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7327 (p : Pattern) (selected : d105323 p = 0) : d106067 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105299 q = 0) : d106053 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105299, d106053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7321 q selected
    | true =>
      simp only [d105299, d106053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105300 q = 0) : d106054 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105300, d106054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105300, d106054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105301 q = 0) : d106055 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105301, d106055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105301, d106055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105302 q = 0) : d106056 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105302, d106056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105302, d106056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105303 q = 0) : d106057 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105303, d106057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105303, d106057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105323 q = 0) : d106067 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105323, d106067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105323, d106067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7328 (p : Pattern) (selected : d105330 p = 0) : d106119 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105280 q = 0) : d106079 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105280, d106079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7317 q selected
    | true =>
      simp only [d105280, d106079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105281 q = 0) : d106080 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105281, d106080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105281, d106080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105282 q = 0) : d106081 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105282, d106081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105282, d106081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105283 q = 0) : d106082 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105283, d106082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105283, d106082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d105287 q = 0) : d106086 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105287, d106086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7318 q selected
    | true =>
      simp only [d105287, d106086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105288 q = 0) : d106087 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105288, d106087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105288, d106087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d105289 q = 0) : d106088 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105289, d106088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d105289, d106088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d105297 q = 0) : d106096 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105297, d106096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7320 q selected
    | true =>
      simp only [d105297, d106096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7313 q selected
  have h9 (q : Pattern) (selected : d105305 q = 0) : d106059 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105305, d106059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7322 q selected
    | true =>
      simp only [d105305, d106059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d105306 q = 0) : d106097 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105306, d106097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d105306, d106097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d105260 q = 0) : d106059 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105260, d106059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7313 q selected
    | true =>
      simp only [d105260, d106059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d105307 q = 0) : d106098 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105307, d106098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d105307, d106098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d105308 q = 0) : d106099 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105308, d106099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d105308, d106099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d105309 q = 0) : d106100 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105309, d106100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d105309, d106100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d105310 q = 0) : d106101 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105310, d106101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105310, d106101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d105313 q = 0) : d106104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105313, d106104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7324 q selected
    | true =>
      simp only [d105313, d106104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d105314 q = 0) : d106105 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105314, d106105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105314, d106105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d105315 q = 0) : d106106 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105315, d106106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d105315, d106106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d105316 q = 0) : d106107 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105316, d106107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105316, d106107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d105318 q = 0) : d106109 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105318, d106109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7325 q selected
    | true =>
      simp only [d105318, d106109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d105319 q = 0) : d106110 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105319, d106110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105319, d106110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d105320 q = 0) : d106111 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105320, d106111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d105320, d106111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d105322 q = 0) : d106113 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105322, d106113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7326 q selected
    | true =>
      simp only [d105322, d106113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7315 q selected
  have h24 (q : Pattern) (selected : d105324 q = 0) : d106068 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105324, d106068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7327 q selected
    | true =>
      simp only [d105324, d106068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d105325 q = 0) : d106114 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105325, d106114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d105325, d106114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d105269 q = 0) : d106068 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105269, d106068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7315 q selected
    | true =>
      simp only [d105269, d106068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d105326 q = 0) : d106115 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105326, d106115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d105326, d106115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d105327 q = 0) : d106116 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105327, d106116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d105327, d106116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d105328 q = 0) : d106117 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105328, d106117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d105328, d106117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d105329 q = 0) : d106118 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105329, d106118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d105329, d106118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d105330 q = 0) : d106119 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105330, d106119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d105330, d106119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro7329 (p : Pattern) (selected : d105332 p = 0) : d106121 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105260 q = 0) : d106059 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105260, d106059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7313 q selected
    | true =>
      simp only [d105260, d106059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105261 q = 0) : d106060 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105261, d106060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105261, d106060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105262 q = 0) : d106061 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105262, d106061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105262, d106061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105263 q = 0) : d106062 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105263, d106062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105263, d106062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d105264 q = 0) : d106063 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105264, d106063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105264, d106063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105332 q = 0) : d106121 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105332, d106121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105332, d106121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7330 (p : Pattern) (selected : d105339 p = 0) : d106128 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105322 q = 0) : d106113 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105322, d106113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7326 q selected
    | true =>
      simp only [d105322, d106113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7315 q selected
  have h2 (q : Pattern) (selected : d105324 q = 0) : d106068 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105324, d106068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7327 q selected
    | true =>
      simp only [d105324, d106068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d105325 q = 0) : d106114 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105325, d106114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105325, d106114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105269 q = 0) : d106068 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105269, d106068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7315 q selected
    | true =>
      simp only [d105269, d106068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105326 q = 0) : d106115 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105326, d106115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105326, d106115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105327 q = 0) : d106116 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105327, d106116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105327, d106116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d105337 q = 0) : d106126 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105337, d106126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105337, d106126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d105338 q = 0) : d106127 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105338, d106127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105338, d106127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d105339 q = 0) : d106128 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105339, d106128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105339, d106128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7331 (p : Pattern) (selected : d105345 p = 0) : d106134 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2357 q = 0) : d53522 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2357, d53522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro616 q selected
    | true =>
      simp only [d2357, d53522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro617 q selected
  have h2 (q : Pattern) (selected : d2358 q = 0) : d53523 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2358, d53523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2358, d53523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2359 q = 0) : d53524 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2359, d53524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2359, d53524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105345 q = 0) : d106134 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d105345, d106134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105345, d106134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7332 (p : Pattern) (selected : d105348 p = 0) : d106137 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2367 q = 0) : d53532 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2367, d53532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro617 q selected
    | true =>
      simp only [d2367, d53532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro618 q selected
  have h2 (q : Pattern) (selected : d2368 q = 0) : d53533 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2368, d53533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2368, d53533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2369 q = 0) : d53534 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2369, d53534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2369, d53534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105348 q = 0) : d106137 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d105348, d106137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105348, d106137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7333 (p : Pattern) (selected : d105354 p = 0) : d106143 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105346 q = 0) : d106135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105346, d106135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7331 q selected
    | true =>
      simp only [d105346, d106135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105347 q = 0) : d106136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105347, d106136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105347, d106136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105349 q = 0) : d106138 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105349, d106138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7332 q selected
    | true =>
      simp only [d105349, d106138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105350 q = 0) : d106139 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105350, d106139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105350, d106139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d105351 q = 0) : d106140 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105351, d106140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105351, d106140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105352 q = 0) : d106141 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105352, d106141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105352, d106141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d105353 q = 0) : d106142 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105353, d106142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d105353, d106142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d105354 q = 0) : d106143 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105354, d106143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d105354, d106143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7334 (p : Pattern) (selected : d105358 p = 0) : d106147 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105349 q = 0) : d106138 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105349, d106138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7332 q selected
    | true =>
      simp only [d105349, d106138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105350 q = 0) : d106139 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105350, d106139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105350, d106139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105355 q = 0) : d106144 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105355, d106144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105355, d106144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105356 q = 0) : d106145 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105356, d106145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105356, d106145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105357 q = 0) : d106146 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105357, d106146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105357, d106146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105358 q = 0) : d106147 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105358, d106147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105358, d106147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7335 (p : Pattern) (selected : d105360 p = 0) : d106137 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2419 q = 0) : d53532 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2419, d53532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro625 q selected
    | true =>
      simp only [d2419, d53532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro626 q selected
  have h2 (q : Pattern) (selected : d2420 q = 0) : d53533 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2420, d53533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2420, d53533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2421 q = 0) : d53534 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2421, d53534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2421, d53534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105360 q = 0) : d106137 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d105360, d106137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105360, d106137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7336 (p : Pattern) (selected : d105366 p = 0) : d106147 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105361 q = 0) : d106138 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105361, d106138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7335 q selected
    | true =>
      simp only [d105361, d106138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105362 q = 0) : d106139 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105362, d106139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105362, d106139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105363 q = 0) : d106144 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105363, d106144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105363, d106144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105364 q = 0) : d106145 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105364, d106145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105364, d106145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105365 q = 0) : d106146 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105365, d106146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105365, d106146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105366 q = 0) : d106147 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105366, d106147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105366, d106147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7337 (p : Pattern) (selected : d105374 p = 0) : d106155 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105359 q = 0) : d106148 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105359, d106148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7333 q selected
    | true =>
      simp only [d105359, d106148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7334 q selected
  have h2 (q : Pattern) (selected : d105367 q = 0) : d106149 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105367, d106149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7336 q selected
    | true =>
      simp only [d105367, d106149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d105368 q = 0) : d106150 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105368, d106150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105368, d106150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105369 q = 0) : d106149 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105369, d106149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7334 q selected
    | true =>
      simp only [d105369, d106149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105370 q = 0) : d106151 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105370, d106151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105370, d106151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105371 q = 0) : d106152 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105371, d106152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105371, d106152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d105372 q = 0) : d106153 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105372, d106153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105372, d106153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d105373 q = 0) : d106154 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105373, d106154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105373, d106154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d105374 q = 0) : d106155 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105374, d106155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105374, d106155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7338 (p : Pattern) (selected : d105380 p = 0) : d106161 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105266 q = 0) : d106065 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105266, d106065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105266, d106065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7314 q selected
  have h2 (q : Pattern) (selected : d105267 q = 0) : d106066 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105267, d106066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105267, d106066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d105275 q = 0) : d106074 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105275, d106074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7314 q selected
    | true =>
      simp only [d105275, d106074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7316 q selected
  have h4 (q : Pattern) (selected : d105276 q = 0) : d106075 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105276, d106075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105276, d106075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105277 q = 0) : d106076 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d105277, d106076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105277, d106076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105331 q = 0) : d106120 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105331, d106120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7323 q selected
    | true =>
      simp only [d105331, d106120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7328 q selected
  have h7 (q : Pattern) (selected : d105333 q = 0) : d106122 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105333, d106122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7329 q selected
    | true =>
      simp only [d105333, d106122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d105334 q = 0) : d106123 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105334, d106123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d105334, d106123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d105335 q = 0) : d106124 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d105335, d106124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d105335, d106124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d105336 q = 0) : d106125 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d105336, d106125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105336, d106125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d105340 q = 0) : d106129 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105340, d106129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105340, d106129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7330 q selected
  have h12 (q : Pattern) (selected : d105341 q = 0) : d106130 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105341, d106130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d105341, d106130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d105342 q = 0) : d106131 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d105342, d106131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d105342, d106131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d105343 q = 0) : d106132 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d105343, d106132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d105343, d106132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d105344 q = 0) : d106133 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d105344, d106133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d105344, d106133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d105375 q = 0) : d106156 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105375, d106156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105375, d106156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7337 q selected
  have h17 (q : Pattern) (selected : d105376 q = 0) : d106157 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105376, d106157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d105376, d106157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d105377 q = 0) : d106158 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d105377, d106158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d105377, d106158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d105378 q = 0) : d106159 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d105378, d106159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d105378, d106159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d105379 q = 0) : d106160 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d105379, d106160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d105379, d106160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d105380 q = 0) : d106161 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d105380, d106161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d105380, d106161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro7339 (p : Pattern) (selected : d105386 p = 0) : d106167 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105381 q = 0) : d106162 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d105381, d106162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105381, d106162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7338 q selected
  have h2 (q : Pattern) (selected : d105382 q = 0) : d106163 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d105382, d106163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105382, d106163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105383 q = 0) : d106164 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d105383, d106164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105383, d106164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105384 q = 0) : d106165 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d105384, d106165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105384, d106165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d105385 q = 0) : d106166 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d105385, d106166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105385, d106166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105386 q = 0) : d106167 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d105386, d106167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105386, d106167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7340 (p : Pattern) (selected : d105392 p = 0) : d106173 p = 1 := by
  have h0 (q : Pattern) (selected : d104841 q = 0) : d105694 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d104841, d105694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7201 q selected
    | true =>
      simp only [d104841, d105694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7227 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d104976 q = 0) : d105811 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d104976, d105811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d104976, d105811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7255 q selected
  have h3 (q : Pattern) (selected : d104977 q = 0) : d105812 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d104977, d105812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104977, d105812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105112 q = 0) : d105929 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d105112, d105929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105112, d105929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7283 q selected
  have h5 (q : Pattern) (selected : d105113 q = 0) : d105930 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d105113, d105930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105113, d105930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105114 q = 0) : d105931 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d105114, d105931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105114, d105931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d105249 q = 0) : d106048 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d105249, d106048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105249, d106048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7311 q selected
  have h8 (q : Pattern) (selected : d105250 q = 0) : d106049 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d105250, d106049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105250, d106049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d105251 q = 0) : d106050 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d105251, d106050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105251, d106050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d105252 q = 0) : d106051 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d105252, d106051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d105252, d106051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d105387 q = 0) : d106168 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d105387, d106168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105387, d106168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7339 q selected
  have h12 (q : Pattern) (selected : d105388 q = 0) : d106169 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d105388, d106169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105388, d106169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d105389 q = 0) : d106170 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d105389, d106170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105389, d106170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d105390 q = 0) : d106171 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d105390, d106171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105390, d106171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d105391 q = 0) : d106172 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d105391, d106172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d105391, d106172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d105392 q = 0) : d106173 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d105392, d106173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d105392, d106173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro7341 (p : Pattern) (selected : d105398 p = 0) : d106179 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105393 q = 0) : d106174 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d105393, d106174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7340 q selected
    | true =>
      simp only [d105393, d106174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105394 q = 0) : d106175 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d105394, d106175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105394, d106175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d105395 q = 0) : d106176 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d105395, d106176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105395, d106176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105396 q = 0) : d106177 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d105396, d106177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105396, d106177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105397 q = 0) : d106178 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d105397, d106178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105397, d106178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105398 q = 0) : d106179 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d105398, d106179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105398, d106179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7342 (p : Pattern) (selected : d105404 p = 0) : d106185 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105399 q = 0) : d106180 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d105399, d106180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7341 q selected
    | true =>
      simp only [d105399, d106180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105400 q = 0) : d106181 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d105400, d106181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105400, d106181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d105401 q = 0) : d106182 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d105401, d106182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105401, d106182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105402 q = 0) : d106183 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d105402, d106183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105402, d106183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105403 q = 0) : d106184 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d105403, d106184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105403, d106184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105404 q = 0) : d106185 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d105404, d106185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105404, d106185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7343 (p : Pattern) (selected : d105410 p = 0) : d106191 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105405 q = 0) : d106186 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d105405, d106186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7342 q selected
    | true =>
      simp only [d105405, d106186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105406 q = 0) : d106187 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d105406, d106187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105406, d106187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d105407 q = 0) : d106188 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d105407, d106188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105407, d106188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105408 q = 0) : d106189 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d105408, d106189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105408, d106189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105409 q = 0) : d106190 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d105409, d106190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105409, d106190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105410 q = 0) : d106191 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d105410, d106191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105410, d106191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7344 (p : Pattern) (selected : d105416 p = 0) : d106197 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105411 q = 0) : d106192 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d105411, d106192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7343 q selected
    | true =>
      simp only [d105411, d106192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105412 q = 0) : d106193 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d105412, d106193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105412, d106193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d105413 q = 0) : d106194 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d105413, d106194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105413, d106194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105414 q = 0) : d106195 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d105414, d106195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105414, d106195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105415 q = 0) : d106196 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d105415, d106196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105415, d106196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105416 q = 0) : d106197 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d105416, d106197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105416, d106197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7345 (p : Pattern) (selected : d105422 p = 0) : d106203 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105417 q = 0) : d106198 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d105417, d106198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7344 q selected
    | true =>
      simp only [d105417, d106198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105418 q = 0) : d106199 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d105418, d106199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105418, d106199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d105419 q = 0) : d106200 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d105419, d106200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105419, d106200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105420 q = 0) : d106201 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d105420, d106201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105420, d106201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105421 q = 0) : d106202 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d105421, d106202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105421, d106202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105422 q = 0) : d106203 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d105422, d106203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105422, d106203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7346 (p : Pattern) (selected : d105428 p = 0) : d106209 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105423 q = 0) : d106204 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d105423, d106204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7345 q selected
    | true =>
      simp only [d105423, d106204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105424 q = 0) : d106205 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d105424, d106205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105424, d106205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d105425 q = 0) : d106206 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d105425, d106206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105425, d106206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105426 q = 0) : d106207 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d105426, d106207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105426, d106207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105427 q = 0) : d106208 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d105427, d106208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105427, d106208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105428 q = 0) : d106209 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d105428, d106209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105428, d106209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7347 (p : Pattern) (selected : d105434 p = 0) : d106215 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105429 q = 0) : d106210 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d105429, d106210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7346 q selected
    | true =>
      simp only [d105429, d106210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105430 q = 0) : d106211 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d105430, d106211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105430, d106211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d105431 q = 0) : d106212 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d105431, d106212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105431, d106212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105432 q = 0) : d106213 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d105432, d106213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105432, d106213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105433 q = 0) : d106214 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d105433, d106214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105433, d106214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105434 q = 0) : d106215 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d105434, d106215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105434, d106215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7348 (p : Pattern) (selected : d104635 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d176 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2 q selected
    | true =>
      simp only [d176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d177 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d178 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d104635 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d104635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7349 (p : Pattern) (selected : d104641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d104636 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7348 q selected
    | true =>
      simp only [d104636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104637 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104638 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104639 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104640 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104641 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7350 (p : Pattern) (selected : d104647 p = 1) : d107192 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d104620 q = 1) : d104620 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d104626 q = 1) : d104626 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d104634 q = 1) : d104634 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d104642 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7349 q selected
    | true =>
      simp only [d104642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104643 q = 1) : d107188 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104643, d107188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104643, d107188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104554 q = 1) : d104554 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d104644 q = 1) : d107189 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104644, d107189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104644, d107189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d104645 q = 1) : d107190 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104645, d107190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104645, d107190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d104646 q = 1) : d107191 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104646, d107191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d104646, d107191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d104647 q = 1) : d107192 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104647, d107192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104647, d107192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro7351 (p : Pattern) (selected : d104659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d104636 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7348 q selected
    | true =>
      simp only [d104636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104637 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104638 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104639 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104640 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104659 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7352 (p : Pattern) (selected : d104665 p = 1) : d107197 p = 1 := by
  have h0 (q : Pattern) (selected : d104620 q = 1) : d104620 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d104626 q = 1) : d104626 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d104634 q = 1) : d104634 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d104642 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7349 q selected
    | true =>
      simp only [d104642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104643 q = 1) : d107188 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104643, d107188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104643, d107188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104554 q = 1) : d104554 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d104644 q = 1) : d107189 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104644, d107189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104644, d107189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d104645 q = 1) : d107190 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104645, d107190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d104645, d107190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d104646 q = 1) : d107191 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104646, d107191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104646, d107191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d104652 q = 1) : d104652 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d104656 q = 1) : d104656 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d104658 q = 1) : d104658 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d104660 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7351 q selected
    | true =>
      simp only [d104660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h14 (q : Pattern) (selected : d104661 q = 1) : d107193 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104661, d107193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d104661, d107193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d104561 q = 1) : d104561 q = 1 := by
    exact selected
  have h16 (q : Pattern) (selected : d104662 q = 1) : d107194 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104662, d107194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d104662, d107194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d104663 q = 1) : d107195 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104663, d107195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d104663, d107195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d104664 q = 1) : d107196 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104664, d107196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d104664, d107196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d104665 q = 1) : d107197 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104665, d107197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d104665, d107197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro7353 (p : Pattern) (selected : d104674 p = 1) : d107204 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d104658 q = 1) : d104658 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d104660 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7351 q selected
    | true =>
      simp only [d104660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d104661 q = 1) : d107193 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104661, d107193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d104661, d107193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d104561 q = 1) : d104561 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d104662 q = 1) : d107194 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104662, d107194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104662, d107194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104672 q = 1) : d107202 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104672, d107202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104672, d107202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d104673 q = 1) : d107203 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104673, d107203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104673, d107203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d104674 q = 1) : d107204 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104674, d107204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104674, d107204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7354 (p : Pattern) (selected : d104688 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (selected : d104688 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d104688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7355 (p : Pattern) (selected : d104694 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d104689 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7354 q selected
    | true =>
      simp only [d104689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104690 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104691 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104692 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104693 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104694 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7356 (p : Pattern) (selected : d104700 p = 1) : d107214 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d104687 q = 1) : d104687 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d104695 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7355 q selected
    | true =>
      simp only [d104695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d104696 q = 1) : d107210 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104696, d107210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d104696, d107210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d104584 q = 1) : d104584 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d104697 q = 1) : d107211 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104697, d107211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104697, d107211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104698 q = 1) : d107212 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104698, d107212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104698, d107212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d104699 q = 1) : d107213 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104699, d107213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104699, d107213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d104700 q = 1) : d107214 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104700, d107214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104700, d107214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7357 (p : Pattern) (selected : d104706 p = 1) : d107220 p = 1 := by
  have h0 (q : Pattern) (selected : d104614 q = 1) : d104614 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d104666 q = 1) : d107198 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d104666, d107198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7350 q selected
    | true =>
      simp only [d104666, d107198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7352 q selected
  have h2 (q : Pattern) (selected : d104668 q = 1) : d104668 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d104669 q = 1) : d107199 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d104669, d107199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d104669, d107199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d104670 q = 1) : d107200 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d104670, d107200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104670, d107200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104671 q = 1) : d107201 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d104671, d107201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104671, d107201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d104675 q = 1) : d107205 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d104675, d107205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104675, d107205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7353 q selected
  have h8 (q : Pattern) (selected : d104676 q = 1) : d107206 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d104676, d107206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d104676, d107206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d104677 q = 1) : d107207 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d104677, d107207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d104677, d107207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d104678 q = 1) : d107208 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d104678, d107208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d104678, d107208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d104679 q = 1) : d107209 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d104679, d107209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d104679, d107209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d104701 q = 1) : d107215 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d104701, d107215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104701, d107215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7356 q selected
  have h13 (q : Pattern) (selected : d104702 q = 1) : d107216 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d104702, d107216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d104702, d107216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d104703 q = 1) : d107217 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d104703, d107217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d104703, d107217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d104704 q = 1) : d107218 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d104704, d107218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d104704, d107218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d104705 q = 1) : d107219 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d104705, d107219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d104705, d107219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d104706 q = 1) : d107220 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d104706, d107220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d104706, d107220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro7358 (p : Pattern) (selected : d104712 p = 1) : d107226 p = 1 := by
  have h0 (q : Pattern) (selected : d104599 q = 1) : d104599 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d104707 q = 1) : d107221 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d104707, d107221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d104707, d107221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7357 q selected
  have h3 (q : Pattern) (selected : d104708 q = 1) : d107222 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d104708, d107222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d104708, d107222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d104709 q = 1) : d107223 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d104709, d107223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d104709, d107223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104710 q = 1) : d107224 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d104710, d107224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d104710, d107224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104711 q = 1) : d107225 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d104711, d107225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d104711, d107225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d104712 q = 1) : d107226 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d104712, d107226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104712, d107226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro7359 (p : Pattern) (selected : d104755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d356 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro16 q selected
    | true =>
      simp only [d356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2 q selected
  have h2 (q : Pattern) (selected : d357 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d358 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d104755 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d104755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7360 (p : Pattern) (selected : d104761 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d104756 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7359 q selected
    | true =>
      simp only [d104756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104757 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104758 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104759 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104760 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104761 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7361 (p : Pattern) (selected : d104768 p = 1) : d107231 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d104740 q = 1) : d104740 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d104746 q = 1) : d104746 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d104754 q = 1) : d104754 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d104762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7360 q selected
    | true =>
      simp only [d104762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104763 q = 1) : d107227 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104763, d107227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104763, d107227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104764 q = 1) : d104764 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d104765 q = 1) : d107228 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104765, d107228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104765, d107228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d104766 q = 1) : d107229 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104766, d107229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104766, d107229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d104767 q = 1) : d107230 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104767, d107230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d104767, d107230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d104768 q = 1) : d107231 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104768, d107231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104768, d107231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro7362 (p : Pattern) (selected : d104780 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d104756 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7359 q selected
    | true =>
      simp only [d104756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104757 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104758 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104759 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104760 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104780 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7363 (p : Pattern) (selected : d104787 p = 1) : d107236 p = 1 := by
  have h0 (q : Pattern) (selected : d104740 q = 1) : d104740 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d104746 q = 1) : d104746 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d104754 q = 1) : d104754 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d104762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7360 q selected
    | true =>
      simp only [d104762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104763 q = 1) : d107227 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104763, d107227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104763, d107227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104764 q = 1) : d104764 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d104765 q = 1) : d107228 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104765, d107228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104765, d107228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d104766 q = 1) : d107229 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104766, d107229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d104766, d107229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d104767 q = 1) : d107230 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104767, d107230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104767, d107230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d104773 q = 1) : d104773 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d104777 q = 1) : d104777 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d104779 q = 1) : d104779 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d104781 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7362 q selected
    | true =>
      simp only [d104781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h14 (q : Pattern) (selected : d104782 q = 1) : d107232 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104782, d107232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d104782, d107232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d104783 q = 1) : d104783 q = 1 := by
    exact selected
  have h16 (q : Pattern) (selected : d104784 q = 1) : d107233 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104784, d107233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d104784, d107233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d104785 q = 1) : d107234 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104785, d107234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d104785, d107234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d104786 q = 1) : d107235 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104786, d107235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d104786, d107235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d104787 q = 1) : d107236 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104787, d107236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d104787, d107236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro7364 (p : Pattern) (selected : d104796 p = 1) : d107243 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d104779 q = 1) : d104779 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d104781 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7362 q selected
    | true =>
      simp only [d104781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d104782 q = 1) : d107232 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104782, d107232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d104782, d107232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d104783 q = 1) : d104783 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d104784 q = 1) : d107233 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104784, d107233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104784, d107233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104794 q = 1) : d107241 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104794, d107241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104794, d107241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d104795 q = 1) : d107242 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104795, d107242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104795, d107242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d104796 q = 1) : d107243 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104796, d107243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104796, d107243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7365 (p : Pattern) (selected : d104814 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (selected : d104814 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d104814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7366 (p : Pattern) (selected : d104820 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d104815 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7365 q selected
    | true =>
      simp only [d104815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104816 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104817 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104818 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104819 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104820 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7367 (p : Pattern) (selected : d104828 p = 1) : d107253 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d104813 q = 1) : d104813 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d104821 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7366 q selected
    | true =>
      simp only [d104821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d104822 q = 1) : d107249 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104822, d107249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d104822, d107249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d104824 q = 1) : d104824 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d104825 q = 1) : d107250 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104825, d107250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104825, d107250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104826 q = 1) : d107251 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104826, d107251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104826, d107251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d104827 q = 1) : d107252 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104827, d107252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104827, d107252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d104828 q = 1) : d107253 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104828, d107253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104828, d107253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7368 (p : Pattern) (selected : d104834 p = 1) : d107259 p = 1 := by
  have h0 (q : Pattern) (selected : d104734 q = 1) : d104734 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d104788 q = 1) : d107237 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d104788, d107237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7361 q selected
    | true =>
      simp only [d104788, d107237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7363 q selected
  have h2 (q : Pattern) (selected : d104790 q = 1) : d104790 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d104791 q = 1) : d107238 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d104791, d107238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d104791, d107238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d104792 q = 1) : d107239 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d104792, d107239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104792, d107239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104793 q = 1) : d107240 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d104793, d107240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104793, d107240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d104797 q = 1) : d107244 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d104797, d107244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104797, d107244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7364 q selected
  have h8 (q : Pattern) (selected : d104798 q = 1) : d107245 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d104798, d107245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d104798, d107245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d104799 q = 1) : d107246 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d104799, d107246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d104799, d107246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d104800 q = 1) : d107247 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d104800, d107247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d104800, d107247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d104801 q = 1) : d107248 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d104801, d107248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d104801, d107248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d104829 q = 1) : d107254 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d104829, d107254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104829, d107254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7367 q selected
  have h13 (q : Pattern) (selected : d104830 q = 1) : d107255 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d104830, d107255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d104830, d107255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d104831 q = 1) : d107256 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d104831, d107256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d104831, d107256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d104832 q = 1) : d107257 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d104832, d107257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d104832, d107257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d104833 q = 1) : d107258 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d104833, d107258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d104833, d107258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d104834 q = 1) : d107259 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d104834, d107259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d104834, d107259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro7369 (p : Pattern) (selected : d104840 p = 1) : d107265 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d104835 q = 1) : d107260 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d104835, d107260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104835, d107260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7368 q selected
  have h2 (q : Pattern) (selected : d104836 q = 1) : d107261 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d104836, d107261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104836, d107261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104837 q = 1) : d107262 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d104837, d107262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104837, d107262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d104838 q = 1) : d107263 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d104838, d107263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104838, d107263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104839 q = 1) : d107264 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d104839, d107264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104839, d107264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104840 q = 1) : d107265 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d104840, d107265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104840, d107265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7370 (p : Pattern) (selected : d104887 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d886 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro54 q selected
    | true =>
      simp only [d886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro55 q selected
  have h2 (q : Pattern) (selected : d887 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d888 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d104887 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d104887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7371 (p : Pattern) (selected : d104893 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d104888 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7370 q selected
    | true =>
      simp only [d104888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104889 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104890 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104891 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104892 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104893 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7372 (p : Pattern) (selected : d104900 p = 1) : d107271 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d104872 q = 1) : d104872 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d104878 q = 1) : d104878 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d104886 q = 1) : d104886 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d104894 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7371 q selected
    | true =>
      simp only [d104894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104895 q = 1) : d107267 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104895, d107267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104895, d107267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104896 q = 1) : d104896 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d104897 q = 1) : d107268 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104897, d107268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104897, d107268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d104898 q = 1) : d107269 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104898, d107269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104898, d107269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d104899 q = 1) : d107270 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104899, d107270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d104899, d107270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d104900 q = 1) : d107271 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104900, d107271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104900, d107271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro7373 (p : Pattern) (selected : d104912 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d104888 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7370 q selected
    | true =>
      simp only [d104888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104889 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104890 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104891 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104892 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104912 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7374 (p : Pattern) (selected : d104919 p = 1) : d107276 p = 1 := by
  have h0 (q : Pattern) (selected : d104872 q = 1) : d104872 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d104878 q = 1) : d104878 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d104886 q = 1) : d104886 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d104894 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7371 q selected
    | true =>
      simp only [d104894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104895 q = 1) : d107267 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104895, d107267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104895, d107267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104896 q = 1) : d104896 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d104897 q = 1) : d107268 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104897, d107268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104897, d107268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d104898 q = 1) : d107269 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104898, d107269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d104898, d107269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d104899 q = 1) : d107270 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104899, d107270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104899, d107270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d104905 q = 1) : d104905 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d104909 q = 1) : d104909 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d104911 q = 1) : d104911 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d104913 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7373 q selected
    | true =>
      simp only [d104913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h14 (q : Pattern) (selected : d104914 q = 1) : d107272 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104914, d107272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d104914, d107272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d104915 q = 1) : d104915 q = 1 := by
    exact selected
  have h16 (q : Pattern) (selected : d104916 q = 1) : d107273 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104916, d107273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d104916, d107273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d104917 q = 1) : d107274 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104917, d107274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d104917, d107274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d104918 q = 1) : d107275 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104918, d107275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d104918, d107275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d104919 q = 1) : d107276 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104919, d107276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d104919, d107276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro7375 (p : Pattern) (selected : d104928 p = 1) : d107283 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d104911 q = 1) : d104911 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d104913 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7373 q selected
    | true =>
      simp only [d104913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d104914 q = 1) : d107272 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104914, d107272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d104914, d107272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d104915 q = 1) : d104915 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d104916 q = 1) : d107273 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104916, d107273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104916, d107273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104926 q = 1) : d107281 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104926, d107281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104926, d107281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d104927 q = 1) : d107282 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104927, d107282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104927, d107282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d104928 q = 1) : d107283 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104928, d107283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104928, d107283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7376 (p : Pattern) (selected : d104949 p = 1) : d0 p = 1 := by
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
  have h4 (q : Pattern) (selected : d104949 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d104949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7377 (p : Pattern) (selected : d104955 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d104950 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d104950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7376 q selected
    | true =>
      simp only [d104950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d104951 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d104951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104952 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d104952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d104952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d104953 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d104953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d104954 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d104954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d104955 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d104955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d104955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7378 (p : Pattern) (selected : d104963 p = 1) : d107293 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d104948 q = 1) : d104948 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d104956 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d104956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7377 q selected
    | true =>
      simp only [d104956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d104957 q = 1) : d107289 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d104957, d107289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d104957, d107289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d104959 q = 1) : d104959 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d104960 q = 1) : d107290 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d104960, d107290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104960, d107290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104961 q = 1) : d107291 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d104961, d107291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104961, d107291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d104962 q = 1) : d107292 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d104962, d107292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104962, d107292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d104963 q = 1) : d107293 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104963, d107293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104963, d107293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7379 (p : Pattern) (selected : d104969 p = 1) : d107299 p = 1 := by
  have h0 (q : Pattern) (selected : d104866 q = 1) : d104866 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d104920 q = 1) : d107277 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d104920, d107277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7372 q selected
    | true =>
      simp only [d104920, d107277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7374 q selected
  have h2 (q : Pattern) (selected : d104922 q = 1) : d104922 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d104923 q = 1) : d107278 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d104923, d107278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d104923, d107278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d104924 q = 1) : d107279 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d104924, d107279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d104924, d107279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104925 q = 1) : d107280 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d104925, d107280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104925, d107280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d104929 q = 1) : d107284 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d104929, d107284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104929, d107284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7375 q selected
  have h8 (q : Pattern) (selected : d104930 q = 1) : d107285 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d104930, d107285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d104930, d107285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d104931 q = 1) : d107286 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d104931, d107286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d104931, d107286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d104932 q = 1) : d107287 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d104932, d107287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d104932, d107287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d104933 q = 1) : d107288 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d104933, d107288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d104933, d107288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d104964 q = 1) : d107294 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d104964, d107294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d104964, d107294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7378 q selected
  have h13 (q : Pattern) (selected : d104965 q = 1) : d107295 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d104965, d107295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d104965, d107295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d104966 q = 1) : d107296 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d104966, d107296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d104966, d107296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d104967 q = 1) : d107297 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d104967, d107297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d104967, d107297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d104968 q = 1) : d107298 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d104968, d107298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d104968, d107298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d104969 q = 1) : d107299 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d104969, d107299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d104969, d107299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro7380 (p : Pattern) (selected : d104975 p = 1) : d107305 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d104970 q = 1) : d107300 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d104970, d107300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104970, d107300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7379 q selected
  have h2 (q : Pattern) (selected : d104971 q = 1) : d107301 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d104971, d107301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104971, d107301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d104972 q = 1) : d107302 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d104972, d107302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104972, d107302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d104973 q = 1) : d107303 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d104973, d107303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104973, d107303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d104974 q = 1) : d107304 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d104974, d107304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104974, d107304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d104975 q = 1) : d107305 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d104975, d107305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104975, d107305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7381 (p : Pattern) (selected : d105023 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1297 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro83 q selected
    | true =>
      simp only [d1297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro85 q selected
  have h2 (q : Pattern) (selected : d1298 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1299 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105023 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d105023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7382 (p : Pattern) (selected : d105029 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d105024 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7381 q selected
    | true =>
      simp only [d105024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105025 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105026 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105027 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105028 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105029 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7383 (p : Pattern) (selected : d105036 p = 1) : d107312 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d105008 q = 1) : d105008 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d105014 q = 1) : d105014 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d105022 q = 1) : d105022 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d105030 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7382 q selected
    | true =>
      simp only [d105030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105031 q = 1) : d107308 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105031, d107308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105031, d107308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105032 q = 1) : d105032 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d105033 q = 1) : d107309 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105033, d107309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105033, d107309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d105034 q = 1) : d107310 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105034, d107310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105034, d107310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d105035 q = 1) : d107311 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105035, d107311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105035, d107311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d105036 q = 1) : d107312 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105036, d107312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105036, d107312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro7384 (p : Pattern) (selected : d105048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d105024 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7381 q selected
    | true =>
      simp only [d105024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105025 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105026 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105027 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105028 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105048 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7385 (p : Pattern) (selected : d105055 p = 1) : d107317 p = 1 := by
  have h0 (q : Pattern) (selected : d105008 q = 1) : d105008 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d105014 q = 1) : d105014 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d105022 q = 1) : d105022 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d105030 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7382 q selected
    | true =>
      simp only [d105030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d105031 q = 1) : d107308 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105031, d107308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105031, d107308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105032 q = 1) : d105032 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d105033 q = 1) : d107309 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105033, d107309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105033, d107309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d105034 q = 1) : d107310 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105034, d107310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105034, d107310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d105035 q = 1) : d107311 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105035, d107311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105035, d107311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d105041 q = 1) : d105041 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d105045 q = 1) : d105045 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d105047 q = 1) : d105047 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d105049 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7384 q selected
    | true =>
      simp only [d105049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h14 (q : Pattern) (selected : d105050 q = 1) : d107313 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105050, d107313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d105050, d107313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d105051 q = 1) : d105051 q = 1 := by
    exact selected
  have h16 (q : Pattern) (selected : d105052 q = 1) : d107314 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105052, d107314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d105052, d107314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d105053 q = 1) : d107315 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105053, d107315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d105053, d107315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d105054 q = 1) : d107316 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105054, d107316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d105054, d107316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d105055 q = 1) : d107317 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105055, d107317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d105055, d107317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro7386 (p : Pattern) (selected : d105064 p = 1) : d107324 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d105047 q = 1) : d105047 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d105049 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7384 q selected
    | true =>
      simp only [d105049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d105050 q = 1) : d107313 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105050, d107313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105050, d107313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105051 q = 1) : d105051 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d105052 q = 1) : d107314 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105052, d107314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105052, d107314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105062 q = 1) : d107322 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105062, d107322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105062, d107322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d105063 q = 1) : d107323 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105063, d107323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105063, d107323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d105064 q = 1) : d107324 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105064, d107324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105064, d107324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7387 (p : Pattern) (selected : d105085 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1464 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro96 q selected
    | true =>
      simp only [d1464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro97 q selected
  have h2 (q : Pattern) (selected : d1465 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1466 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105085 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d105085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7388 (p : Pattern) (selected : d105091 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d105086 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7387 q selected
    | true =>
      simp only [d105086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105087 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105088 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105089 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105090 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105091 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7389 (p : Pattern) (selected : d105099 p = 1) : d107334 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d105084 q = 1) : d105084 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d105092 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7388 q selected
    | true =>
      simp only [d105092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d105093 q = 1) : d107330 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105093, d107330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105093, d107330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105095 q = 1) : d105095 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d105096 q = 1) : d107331 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105096, d107331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105096, d107331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105097 q = 1) : d107332 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105097, d107332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105097, d107332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d105098 q = 1) : d107333 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105098, d107333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105098, d107333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d105099 q = 1) : d107334 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105099, d107334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105099, d107334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7390 (p : Pattern) (selected : d105105 p = 1) : d107340 p = 1 := by
  have h0 (q : Pattern) (selected : d105002 q = 1) : d105002 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d105056 q = 1) : d107318 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105056, d107318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7383 q selected
    | true =>
      simp only [d105056, d107318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7385 q selected
  have h2 (q : Pattern) (selected : d105058 q = 1) : d105058 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d105059 q = 1) : d107319 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105059, d107319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105059, d107319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d105060 q = 1) : d107320 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d105060, d107320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105060, d107320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105061 q = 1) : d107321 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d105061, d107321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105061, d107321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d105065 q = 1) : d107325 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105065, d107325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105065, d107325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7386 q selected
  have h8 (q : Pattern) (selected : d105066 q = 1) : d107326 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105066, d107326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d105066, d107326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d105067 q = 1) : d107327 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d105067, d107327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d105067, d107327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d105068 q = 1) : d107328 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d105068, d107328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d105068, d107328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d105069 q = 1) : d107329 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d105069, d107329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d105069, d107329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d105100 q = 1) : d107335 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105100, d107335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105100, d107335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7389 q selected
  have h13 (q : Pattern) (selected : d105101 q = 1) : d107336 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105101, d107336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d105101, d107336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d105102 q = 1) : d107337 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d105102, d107337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d105102, d107337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d105103 q = 1) : d107338 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d105103, d107338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d105103, d107338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d105104 q = 1) : d107339 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d105104, d107339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d105104, d107339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d105105 q = 1) : d107340 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d105105, d107340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d105105, d107340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro7391 (p : Pattern) (selected : d105111 p = 1) : d107346 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d105106 q = 1) : d107341 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d105106, d107341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105106, d107341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7390 q selected
  have h2 (q : Pattern) (selected : d105107 q = 1) : d107342 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d105107, d107342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105107, d107342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105108 q = 1) : d107343 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d105108, d107343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105108, d107343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105109 q = 1) : d107344 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d105109, d107344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105109, d107344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d105110 q = 1) : d107345 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d105110, d107345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105110, d107345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105111 q = 1) : d107346 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d105111, d107346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105111, d107346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7392 (p : Pattern) (selected : d105160 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1774 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro119 q selected
    | true =>
      simp only [d1774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro121 q selected
  have h2 (q : Pattern) (selected : d1775 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1776 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105160 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d105160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7393 (p : Pattern) (selected : d105166 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d105161 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7392 q selected
    | true =>
      simp only [d105161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105162 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105163 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105164 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105165 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105166 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7394 (p : Pattern) (selected : d105173 p = 1) : d107354 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d105145 q = 1) : d105145 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d105151 q = 1) : d105151 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d105159 q = 1) : d105159 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d105167 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7393 q selected
    | true =>
      simp only [d105167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105168 q = 1) : d107350 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105168, d107350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105168, d107350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105169 q = 1) : d105169 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d105170 q = 1) : d107351 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105170, d107351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105170, d107351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d105171 q = 1) : d107352 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105171, d107352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105171, d107352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d105172 q = 1) : d107353 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105172, d107353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105172, d107353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d105173 q = 1) : d107354 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105173, d107354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105173, d107354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro7395 (p : Pattern) (selected : d105185 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d105161 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7392 q selected
    | true =>
      simp only [d105161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105162 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105163 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105164 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105165 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105185 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7396 (p : Pattern) (selected : d105192 p = 1) : d107359 p = 1 := by
  have h0 (q : Pattern) (selected : d105145 q = 1) : d105145 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d105151 q = 1) : d105151 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d105159 q = 1) : d105159 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d105167 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7393 q selected
    | true =>
      simp only [d105167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d105168 q = 1) : d107350 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105168, d107350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105168, d107350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105169 q = 1) : d105169 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d105170 q = 1) : d107351 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105170, d107351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105170, d107351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d105171 q = 1) : d107352 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105171, d107352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105171, d107352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d105172 q = 1) : d107353 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105172, d107353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105172, d107353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d105178 q = 1) : d105178 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d105182 q = 1) : d105182 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d105184 q = 1) : d105184 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d105186 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7395 q selected
    | true =>
      simp only [d105186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h14 (q : Pattern) (selected : d105187 q = 1) : d107355 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105187, d107355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d105187, d107355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d105188 q = 1) : d105188 q = 1 := by
    exact selected
  have h16 (q : Pattern) (selected : d105189 q = 1) : d107356 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105189, d107356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d105189, d107356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d105190 q = 1) : d107357 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105190, d107357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d105190, d107357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d105191 q = 1) : d107358 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105191, d107358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d105191, d107358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d105192 q = 1) : d107359 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105192, d107359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d105192, d107359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro7397 (p : Pattern) (selected : d105201 p = 1) : d107366 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d105184 q = 1) : d105184 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d105186 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7395 q selected
    | true =>
      simp only [d105186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d105187 q = 1) : d107355 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105187, d107355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105187, d107355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105188 q = 1) : d105188 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d105189 q = 1) : d107356 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105189, d107356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105189, d107356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105199 q = 1) : d107364 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105199, d107364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105199, d107364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d105200 q = 1) : d107365 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105200, d107365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105200, d107365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d105201 q = 1) : d107366 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105201, d107366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105201, d107366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7398 (p : Pattern) (selected : d105222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1941 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro132 q selected
    | true =>
      simp only [d1941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro133 q selected
  have h2 (q : Pattern) (selected : d1942 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1943 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105222 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d105222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7399 (p : Pattern) (selected : d105228 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d105223 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7398 q selected
    | true =>
      simp only [d105223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105224 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105225 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105226 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105227 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105228 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7400 (p : Pattern) (selected : d105236 p = 1) : d107376 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d105221 q = 1) : d105221 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d105229 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7399 q selected
    | true =>
      simp only [d105229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d105230 q = 1) : d107372 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105230, d107372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105230, d107372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105232 q = 1) : d105232 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d105233 q = 1) : d107373 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105233, d107373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105233, d107373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105234 q = 1) : d107374 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105234, d107374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105234, d107374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d105235 q = 1) : d107375 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105235, d107375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105235, d107375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d105236 q = 1) : d107376 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105236, d107376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105236, d107376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7401 (p : Pattern) (selected : d105242 p = 1) : d107382 p = 1 := by
  have h0 (q : Pattern) (selected : d105139 q = 1) : d105139 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d105193 q = 1) : d107360 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105193, d107360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7394 q selected
    | true =>
      simp only [d105193, d107360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7396 q selected
  have h2 (q : Pattern) (selected : d105195 q = 1) : d105195 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d105196 q = 1) : d107361 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105196, d107361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105196, d107361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d105197 q = 1) : d107362 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d105197, d107362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105197, d107362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105198 q = 1) : d107363 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d105198, d107363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105198, d107363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d105202 q = 1) : d107367 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105202, d107367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105202, d107367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7397 q selected
  have h8 (q : Pattern) (selected : d105203 q = 1) : d107368 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105203, d107368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d105203, d107368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d105204 q = 1) : d107369 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d105204, d107369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d105204, d107369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d105205 q = 1) : d107370 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d105205, d107370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d105205, d107370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d105206 q = 1) : d107371 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d105206, d107371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d105206, d107371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d105237 q = 1) : d107377 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105237, d107377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105237, d107377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7400 q selected
  have h13 (q : Pattern) (selected : d105238 q = 1) : d107378 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105238, d107378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d105238, d107378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d105239 q = 1) : d107379 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d105239, d107379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d105239, d107379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d105240 q = 1) : d107380 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d105240, d107380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d105240, d107380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d105241 q = 1) : d107381 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d105241, d107381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d105241, d107381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d105242 q = 1) : d107382 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d105242, d107382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d105242, d107382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro7402 (p : Pattern) (selected : d105248 p = 1) : d107388 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d105243 q = 1) : d107383 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d105243, d107383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105243, d107383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7401 q selected
  have h2 (q : Pattern) (selected : d105244 q = 1) : d107384 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d105244, d107384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105244, d107384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105245 q = 1) : d107385 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d105245, d107385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105245, d107385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105246 q = 1) : d107386 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d105246, d107386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105246, d107386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d105247 q = 1) : d107387 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d105247, d107387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105247, d107387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105248 q = 1) : d107388 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d105248, d107388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105248, d107388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7403 (p : Pattern) (selected : d105298 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2252 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro156 q selected
    | true =>
      simp only [d2252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro158 q selected
  have h2 (q : Pattern) (selected : d2253 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2254 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105298 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d105298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7404 (p : Pattern) (selected : d105304 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d105299 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7403 q selected
    | true =>
      simp only [d105299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105301 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105302 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105303 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105304 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7405 (p : Pattern) (selected : d105311 p = 1) : d107397 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d105283 q = 1) : d105283 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d105289 q = 1) : d105289 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d105297 q = 1) : d105297 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d105305 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7404 q selected
    | true =>
      simp only [d105305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105306 q = 1) : d107393 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105306, d107393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105306, d107393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105307 q = 1) : d105307 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d105308 q = 1) : d107394 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105308, d107394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105308, d107394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d105309 q = 1) : d107395 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105309, d107395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105309, d107395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d105310 q = 1) : d107396 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105310, d107396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105310, d107396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d105311 q = 1) : d107397 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105311, d107397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105311, d107397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro7406 (p : Pattern) (selected : d105323 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d105299 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7403 q selected
    | true =>
      simp only [d105299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105300 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105301 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105302 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105303 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105323 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7407 (p : Pattern) (selected : d105330 p = 1) : d107402 p = 1 := by
  have h0 (q : Pattern) (selected : d105283 q = 1) : d105283 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d105289 q = 1) : d105289 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d105297 q = 1) : d105297 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d105305 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7404 q selected
    | true =>
      simp only [d105305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d105306 q = 1) : d107393 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105306, d107393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105306, d107393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105307 q = 1) : d105307 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d105308 q = 1) : d107394 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105308, d107394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105308, d107394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d105309 q = 1) : d107395 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105309, d107395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105309, d107395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d105310 q = 1) : d107396 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105310, d107396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105310, d107396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d105316 q = 1) : d105316 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d105320 q = 1) : d105320 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d105322 q = 1) : d105322 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d105324 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7406 q selected
    | true =>
      simp only [d105324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h14 (q : Pattern) (selected : d105325 q = 1) : d107398 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105325, d107398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d105325, d107398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d105326 q = 1) : d105326 q = 1 := by
    exact selected
  have h16 (q : Pattern) (selected : d105327 q = 1) : d107399 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105327, d107399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d105327, d107399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d105328 q = 1) : d107400 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105328, d107400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d105328, d107400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d105329 q = 1) : d107401 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105329, d107401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d105329, d107401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d105330 q = 1) : d107402 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105330, d107402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d105330, d107402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro7408 (p : Pattern) (selected : d105339 p = 1) : d107409 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d105322 q = 1) : d105322 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d105324 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7406 q selected
    | true =>
      simp only [d105324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d105325 q = 1) : d107398 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105325, d107398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105325, d107398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105326 q = 1) : d105326 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d105327 q = 1) : d107399 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105327, d107399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105327, d107399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105337 q = 1) : d107407 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105337, d107407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105337, d107407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d105338 q = 1) : d107408 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105338, d107408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105338, d107408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d105339 q = 1) : d107409 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105339, d107409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105339, d107409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7409 (p : Pattern) (selected : d105360 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2419 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro169 q selected
    | true =>
      simp only [d2419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro170 q selected
  have h2 (q : Pattern) (selected : d2420 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2421 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105360 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d105360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro7410 (p : Pattern) (selected : d105366 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d105361 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d105361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7409 q selected
    | true =>
      simp only [d105361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105362 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d105362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105363 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d105363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105364 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d105364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105365 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d105365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105366 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d105366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7411 (p : Pattern) (selected : d105374 p = 1) : d107419 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d105359 q = 1) : d105359 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d105367 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d105367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7410 q selected
    | true =>
      simp only [d105367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d105368 q = 1) : d107415 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d105368, d107415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105368, d107415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105370 q = 1) : d105370 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d105371 q = 1) : d107416 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d105371, d107416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105371, d107416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105372 q = 1) : d107417 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d105372, d107417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105372, d107417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d105373 q = 1) : d107418 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d105373, d107418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105373, d107418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d105374 q = 1) : d107419 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d105374, d107419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105374, d107419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7412 (p : Pattern) (selected : d105380 p = 1) : d107425 p = 1 := by
  have h0 (q : Pattern) (selected : d105277 q = 1) : d105277 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d105331 q = 1) : d107403 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105331, d107403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7405 q selected
    | true =>
      simp only [d105331, d107403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7407 q selected
  have h2 (q : Pattern) (selected : d105333 q = 1) : d105333 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d105334 q = 1) : d107404 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105334, d107404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105334, d107404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d105335 q = 1) : d107405 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d105335, d107405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105335, d107405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105336 q = 1) : d107406 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d105336, d107406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105336, d107406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d105340 q = 1) : d107410 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105340, d107410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105340, d107410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7408 q selected
  have h8 (q : Pattern) (selected : d105341 q = 1) : d107411 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105341, d107411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d105341, d107411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d105342 q = 1) : d107412 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d105342, d107412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d105342, d107412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d105343 q = 1) : d107413 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d105343, d107413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d105343, d107413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d105344 q = 1) : d107414 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d105344, d107414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d105344, d107414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d105375 q = 1) : d107420 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105375, d107420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105375, d107420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7411 q selected
  have h13 (q : Pattern) (selected : d105376 q = 1) : d107421 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d105376, d107421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d105376, d107421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d105377 q = 1) : d107422 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d105377, d107422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d105377, d107422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d105378 q = 1) : d107423 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d105378, d107423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d105378, d107423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d105379 q = 1) : d107424 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d105379, d107424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d105379, d107424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d105380 q = 1) : d107425 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d105380, d107425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d105380, d107425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro7413 (p : Pattern) (selected : d105386 p = 1) : d107431 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d105381 q = 1) : d107426 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d105381, d107426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105381, d107426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7412 q selected
  have h2 (q : Pattern) (selected : d105382 q = 1) : d107427 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d105382, d107427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105382, d107427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d105383 q = 1) : d107428 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d105383, d107428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105383, d107428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105384 q = 1) : d107429 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d105384, d107429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105384, d107429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d105385 q = 1) : d107430 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d105385, d107430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105385, d107430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105386 q = 1) : d107431 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d105386, d107431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105386, d107431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7414 (p : Pattern) (selected : d105392 p = 1) : d107437 p = 1 := by
  have h0 (q : Pattern) (selected : d104841 q = 1) : d107266 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d104841, d107266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7358 q selected
    | true =>
      simp only [d104841, d107266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7369 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d104976 q = 1) : d107306 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d104976, d107306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d104976, d107306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7380 q selected
  have h3 (q : Pattern) (selected : d104977 q = 1) : d107307 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d104977, d107307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d104977, d107307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d105112 q = 1) : d107347 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d105112, d107347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105112, d107347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7391 q selected
  have h5 (q : Pattern) (selected : d105113 q = 1) : d107348 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d105113, d107348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105113, d107348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d105114 q = 1) : d107349 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d105114, d107349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105114, d107349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d105249 q = 1) : d107389 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d105249, d107389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105249, d107389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7402 q selected
  have h8 (q : Pattern) (selected : d105250 q = 1) : d107390 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d105250, d107390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105250, d107390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d105251 q = 1) : d107391 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d105251, d107391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105251, d107391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d105252 q = 1) : d107392 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d105252, d107392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d105252, d107392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d105387 q = 1) : d107432 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d105387, d107432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105387, d107432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7413 q selected
  have h12 (q : Pattern) (selected : d105388 q = 1) : d107433 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d105388, d107433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105388, d107433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d105389 q = 1) : d107434 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d105389, d107434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105389, d107434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d105390 q = 1) : d107435 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d105390, d107435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105390, d107435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d105391 q = 1) : d107436 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d105391, d107436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d105391, d107436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d105392 q = 1) : d107437 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d105392, d107437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d105392, d107437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro7415 (p : Pattern) (selected : d105398 p = 1) : d107443 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d105393 q = 1) : d107438 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d105393, d107438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7414 q selected
    | true =>
      simp only [d105393, d107438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105394 q = 1) : d107439 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d105394, d107439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105394, d107439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d105395 q = 1) : d107440 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d105395, d107440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105395, d107440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105396 q = 1) : d107441 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d105396, d107441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105396, d107441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105397 q = 1) : d107442 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d105397, d107442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105397, d107442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105398 q = 1) : d107443 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d105398, d107443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105398, d107443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7416 (p : Pattern) (selected : d105404 p = 1) : d107449 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d105399 q = 1) : d107444 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d105399, d107444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7415 q selected
    | true =>
      simp only [d105399, d107444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105400 q = 1) : d107445 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d105400, d107445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105400, d107445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d105401 q = 1) : d107446 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d105401, d107446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105401, d107446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105402 q = 1) : d107447 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d105402, d107447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105402, d107447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105403 q = 1) : d107448 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d105403, d107448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105403, d107448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105404 q = 1) : d107449 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d105404, d107449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105404, d107449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7417 (p : Pattern) (selected : d105410 p = 1) : d107455 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d105405 q = 1) : d107450 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d105405, d107450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7416 q selected
    | true =>
      simp only [d105405, d107450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105406 q = 1) : d107451 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d105406, d107451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105406, d107451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d105407 q = 1) : d107452 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d105407, d107452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105407, d107452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105408 q = 1) : d107453 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d105408, d107453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105408, d107453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105409 q = 1) : d107454 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d105409, d107454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105409, d107454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105410 q = 1) : d107455 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d105410, d107455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105410, d107455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7418 (p : Pattern) (selected : d105416 p = 1) : d107461 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d105411 q = 1) : d107456 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d105411, d107456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7417 q selected
    | true =>
      simp only [d105411, d107456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105412 q = 1) : d107457 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d105412, d107457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105412, d107457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d105413 q = 1) : d107458 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d105413, d107458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105413, d107458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105414 q = 1) : d107459 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d105414, d107459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105414, d107459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105415 q = 1) : d107460 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d105415, d107460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105415, d107460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105416 q = 1) : d107461 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d105416, d107461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105416, d107461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7419 (p : Pattern) (selected : d105422 p = 1) : d107467 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d105417 q = 1) : d107462 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d105417, d107462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7418 q selected
    | true =>
      simp only [d105417, d107462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105418 q = 1) : d107463 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d105418, d107463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105418, d107463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d105419 q = 1) : d107464 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d105419, d107464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105419, d107464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105420 q = 1) : d107465 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d105420, d107465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105420, d107465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105421 q = 1) : d107466 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d105421, d107466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105421, d107466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105422 q = 1) : d107467 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d105422, d107467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105422, d107467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7420 (p : Pattern) (selected : d105428 p = 1) : d107473 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d105423 q = 1) : d107468 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d105423, d107468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7419 q selected
    | true =>
      simp only [d105423, d107468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105424 q = 1) : d107469 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d105424, d107469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105424, d107469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d105425 q = 1) : d107470 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d105425, d107470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105425, d107470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105426 q = 1) : d107471 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d105426, d107471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105426, d107471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105427 q = 1) : d107472 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d105427, d107472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105427, d107472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105428 q = 1) : d107473 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d105428, d107473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105428, d107473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7421 (p : Pattern) (selected : d105434 p = 1) : d107479 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d105429 q = 1) : d107474 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d105429, d107474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7420 q selected
    | true =>
      simp only [d105429, d107474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d105430 q = 1) : d107475 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d105430, d107475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d105430, d107475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d105431 q = 1) : d107476 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d105431, d107476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d105431, d107476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d105432 q = 1) : d107477 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d105432, d107477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d105432, d107477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d105433 q = 1) : d107478 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d105433, d107478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d105433, d107478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d105434 q = 1) : d107479 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d105434, d107479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d105434, d107479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7422 (p : Pattern) (selected : d10654 p = 0) : d107491 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10649 q = 0) : d107486 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, d107486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro206 q selected
    | true =>
      simp only [d10649, d107486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10650 q = 0) : d107487 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d107487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10650, d107487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10651 q = 0) : d107488 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d107488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10651, d107488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d31 q = 0) : d51883 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro188 q selected
    | true =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d32 q = 0) : d51884 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d33 q = 0) : d51885 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10652 q = 0) : d107489 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10652, d107489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10652, d107489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d34 q = 0) : d51886 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, d51886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d34, d51886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10653 q = 0) : d107490 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10653, d107490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10653, d107490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10654 q = 0) : d107491 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10654, d107491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10654, d107491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro7423 (p : Pattern) (selected : d10660 p = 0) : d107497 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10655 q = 0) : d107492 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d107492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7422 q selected
    | true =>
      simp only [d10655, d107492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10656 q = 0) : d107493 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d107493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10656, d107493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d37 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro189 q selected
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d38 q = 0) : d51890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10657 q = 0) : d107494 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d107494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10657, d107494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10658 q = 0) : d107495 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10658, d107495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10658, d107495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10659 q = 0) : d107496 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10659, d107496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10659, d107496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10660 q = 0) : d107497 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10660, d107497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10660, d107497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7424 (p : Pattern) (selected : d10666 p = 0) : d107503 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117 q = 0) : d51969 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro202 q selected
    | true =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118 q = 0) : d51970 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d119 q = 0) : d51971 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d120 q = 0) : d51972 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d124 q = 0) : d51976 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro203 q selected
    | true =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d125 q = 0) : d51977 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d126 q = 0) : d51978 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10661 q = 0) : d107498 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d107498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7423 q selected
    | true =>
      simp only [d10661, d107498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
  have h9 (q : Pattern) (selected : d188 q = 0) : d51895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro213 q selected
    | true =>
      simp only [d188, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d10662 q = 0) : d107499 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10662, d107499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10662, d107499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d43 q = 0) : d51895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d44 q = 0) : d51896 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d10663 q = 0) : d107500 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10663, d107500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d10663, d107500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d10664 q = 0) : d107501 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10664, d107501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10664, d107501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d10665 q = 0) : d107502 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10665, d107502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10665, d107502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d10666 q = 0) : d107503 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10666, d107503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10666, d107503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro7425 (p : Pattern) (selected : d10667 p = 0) : d107504 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10655 q = 0) : d107492 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d107492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7422 q selected
    | true =>
      simp only [d10655, d107492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10656 q = 0) : d107493 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d107493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10656, d107493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d37 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro189 q selected
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d38 q = 0) : d51890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10657 q = 0) : d107494 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d107494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10657, d107494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10658 q = 0) : d107495 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10658, d107495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10658, d107495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10659 q = 0) : d107496 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10659, d107496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10659, d107496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10667 q = 0) : d107504 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10667, d107504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10667, d107504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7426 (p : Pattern) (selected : d10673 p = 0) : d107510 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d117 q = 0) : d51969 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro202 q selected
    | true =>
      simp only [d117, d51969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d118 q = 0) : d51970 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d118, d51970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d119 q = 0) : d51971 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d119, d51971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d120 q = 0) : d51972 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d120, d51972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d124 q = 0) : d51976 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro203 q selected
    | true =>
      simp only [d124, d51976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d125 q = 0) : d51977 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d125, d51977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d126 q = 0) : d51978 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d126, d51978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10661 q = 0) : d107498 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d107498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7423 q selected
    | true =>
      simp only [d10661, d107498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
  have h9 (q : Pattern) (selected : d188 q = 0) : d51895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d188, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro213 q selected
    | true =>
      simp only [d188, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d10662 q = 0) : d107499 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10662, d107499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10662, d107499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d43 q = 0) : d51895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d44 q = 0) : d51896 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d10663 q = 0) : d107500 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10663, d107500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d10663, d107500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d10664 q = 0) : d107501 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10664, d107501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10664, d107501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d10665 q = 0) : d107502 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10665, d107502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10665, d107502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d195 q = 0) : d52015 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, d52015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro215 q selected
    | true =>
      simp only [d195, d52015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d196 q = 0) : d52016 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, d52016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d196, d52016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d197 q = 0) : d52017 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, d52017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d197, d52017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d198 q = 0) : d52018 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, d52018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d198, d52018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d200 q = 0) : d52020 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, d52020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro216 q selected
    | true =>
      simp only [d200, d52020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d201 q = 0) : d52021 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, d52021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d201, d52021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d202 q = 0) : d52022 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, d52022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d202, d52022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d10668 q = 0) : d107505 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10668, d107505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7425 q selected
    | true =>
      simp only [d10668, d107505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro192 q selected
  have h24 (q : Pattern) (selected : d206 q = 0) : d51902 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d206, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro218 q selected
    | true =>
      simp only [d206, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d10669 q = 0) : d107506 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10669, d107506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d10669, d107506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d50 q = 0) : d51902 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro192 q selected
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d51 q = 0) : d51903 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d10670 q = 0) : d107507 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10670, d107507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d10670, d107507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d10671 q = 0) : d107508 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10671, d107508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d10671, d107508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d10672 q = 0) : d107509 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10672, d107509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d10672, d107509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d10673 q = 0) : d107510 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10673, d107510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d10673, d107510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro7427 (p : Pattern) (selected : d10680 p = 0) : d107517 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10668 q = 0) : d107505 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10668, d107505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7425 q selected
    | true =>
      simp only [d10668, d107505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro192 q selected
  have h2 (q : Pattern) (selected : d206 q = 0) : d51902 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d206, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro218 q selected
    | true =>
      simp only [d206, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10669 q = 0) : d107506 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10669, d107506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10669, d107506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d50 q = 0) : d51902 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro192 q selected
    | true =>
      simp only [d50, d51902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d51 q = 0) : d51903 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d51, d51903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10670 q = 0) : d107507 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10670, d107507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10670, d107507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10678 q = 0) : d107515 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10678, d107515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10678, d107515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10679 q = 0) : d107516 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10679, d107516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10679, d107516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10680 q = 0) : d107517 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10680, d107517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10680, d107517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7428 (p : Pattern) (selected : d10691 p = 0) : d107528 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10686 q = 0) : d107523 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, d107523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro222 q selected
    | true =>
      simp only [d10686, d107523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10687 q = 0) : d107524 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d107524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10687, d107524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10688 q = 0) : d107525 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d107525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10688, d107525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
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
  have h7 (q : Pattern) (selected : d10689 q = 0) : d107526 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10689, d107526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10689, d107526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
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
  have h9 (q : Pattern) (selected : d10690 q = 0) : d107527 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10690, d107527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10690, d107527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10691 q = 0) : d107528 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10691, d107528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10691, d107528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro7429 (p : Pattern) (selected : d10697 p = 0) : d107534 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10692 q = 0) : d107529 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10692, d107529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7428 q selected
    | true =>
      simp only [d10692, d107529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10693 q = 0) : d107530 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10693, d107530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10693, d107530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d78 q = 0) : d51930 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, d51930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro196 q selected
    | true =>
      simp only [d78, d51930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d79 q = 0) : d51931 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, d51931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d79, d51931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10694 q = 0) : d107531 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10694, d107531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10694, d107531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10695 q = 0) : d107532 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10695, d107532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10695, d107532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10696 q = 0) : d107533 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10696, d107533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10696, d107533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10697 q = 0) : d107534 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10697, d107534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10697, d107534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7430 (p : Pattern) (selected : d10703 p = 0) : d107540 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10698 q = 0) : d107535 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10698, d107535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7429 q selected
    | true =>
      simp only [d10698, d107535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro197 q selected
  have h2 (q : Pattern) (selected : d263 q = 0) : d51936 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d263, d51936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro227 q selected
    | true =>
      simp only [d263, d51936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10699 q = 0) : d107536 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10699, d107536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10699, d107536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d84 q = 0) : d51936 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro197 q selected
    | true =>
      simp only [d84, d51936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d85 q = 0) : d51937 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, d51937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d85, d51937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10700 q = 0) : d107537 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10700, d107537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10700, d107537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10701 q = 0) : d107538 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10701, d107538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10701, d107538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10702 q = 0) : d107539 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10702, d107539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10702, d107539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10703 q = 0) : d107540 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10703, d107540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10703, d107540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7431 (p : Pattern) (selected : d10709 p = 0) : d107546 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d105 q = 0) : d51957 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, d51957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105, d51957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro200 q selected
  have h2 (q : Pattern) (selected : d106 q = 0) : d51958 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, d51958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d106, d51958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d112 q = 0) : d51964 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, d51964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro200 q selected
    | true =>
      simp only [d112, d51964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro201 q selected
  have h4 (q : Pattern) (selected : d113 q = 0) : d51965 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, d51965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d113, d51965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d114 q = 0) : d51966 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, d51966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d114, d51966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10674 q = 0) : d107511 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10674, d107511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7424 q selected
    | true =>
      simp only [d10674, d107511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7426 q selected
  have h7 (q : Pattern) (selected : d214 q = 0) : d52032 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro220 q selected
    | true =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10675 q = 0) : d107512 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10675, d107512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10675, d107512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10676 q = 0) : d107513 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d10676, d107513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10676, d107513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d10677 q = 0) : d107514 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d10677, d107514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10677, d107514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10681 q = 0) : d107518 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10681, d107518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10681, d107518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7427 q selected
  have h12 (q : Pattern) (selected : d10682 q = 0) : d107519 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10682, d107519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d10682, d107519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d10683 q = 0) : d107520 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d10683, d107520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d10683, d107520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d10684 q = 0) : d107521 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d10684, d107521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d10684, d107521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d10685 q = 0) : d107522 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d10685, d107522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d10685, d107522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d10704 q = 0) : d107541 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10704, d107541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10704, d107541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7430 q selected
  have h17 (q : Pattern) (selected : d10705 q = 0) : d107542 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10705, d107542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d10705, d107542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d10706 q = 0) : d107543 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d10706, d107543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d10706, d107543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d10707 q = 0) : d107544 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d10707, d107544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d10707, d107544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d10708 q = 0) : d107545 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d10708, d107545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d10708, d107545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d10709 q = 0) : d107546 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d10709, d107546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d10709, d107546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro7432 (p : Pattern) (selected : d10719 p = 0) : d107556 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10661 q = 0) : d107498 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d107498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7423 q selected
    | true =>
      simp only [d10661, d107498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
  have h2 (q : Pattern) (selected : d10715 q = 0) : d107552 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10715, d107552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10715, d107552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10716 q = 0) : d107553 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10716, d107553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10716, d107553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10717 q = 0) : d107554 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10717, d107554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10717, d107554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10718 q = 0) : d107555 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10718, d107555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10718, d107555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10719 q = 0) : d107556 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10719, d107556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10719, d107556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7433 (p : Pattern) (selected : d10726 p = 0) : d107563 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10661 q = 0) : d107498 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d107498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7423 q selected
    | true =>
      simp only [d10661, d107498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
  have h2 (q : Pattern) (selected : d10715 q = 0) : d107552 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10715, d107552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10715, d107552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10716 q = 0) : d107553 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10716, d107553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10716, d107553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10717 q = 0) : d107554 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10717, d107554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10717, d107554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10718 q = 0) : d107555 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10718, d107555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10718, d107555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10668 q = 0) : d107505 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10668, d107505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7425 q selected
    | true =>
      simp only [d10668, d107505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro192 q selected
  have h7 (q : Pattern) (selected : d10722 q = 0) : d107559 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10722, d107559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10722, d107559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10723 q = 0) : d107560 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10723, d107560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10723, d107560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10724 q = 0) : d107561 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10724, d107561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10724, d107561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10725 q = 0) : d107562 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10725, d107562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10725, d107562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10726 q = 0) : d107563 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10726, d107563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10726, d107563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro7434 (p : Pattern) (selected : d10731 p = 0) : d107568 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10655 q = 0) : d107492 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d107492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7422 q selected
    | true =>
      simp only [d10655, d107492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10656 q = 0) : d107493 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d107493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10656, d107493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d37 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro189 q selected
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d38 q = 0) : d51890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10657 q = 0) : d107494 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d107494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10657, d107494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10658 q = 0) : d107495 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10658, d107495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10658, d107495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10730 q = 0) : d107567 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10730, d107567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10730, d107567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10731 q = 0) : d107568 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10731, d107568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10731, d107568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7435 (p : Pattern) (selected : d10738 p = 0) : d107575 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10655 q = 0) : d107492 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d107492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7422 q selected
    | true =>
      simp only [d10655, d107492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10656 q = 0) : d107493 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d107493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10656, d107493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d37 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro189 q selected
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d38 q = 0) : d51890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10657 q = 0) : d107494 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d107494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10657, d107494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10736 q = 0) : d107573 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10736, d107573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10736, d107573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10737 q = 0) : d107574 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10737, d107574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10737, d107574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10738 q = 0) : d107575 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10738, d107575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10738, d107575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7436 (p : Pattern) (selected : d10747 p = 0) : d107584 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10742 q = 0) : d107579 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10742, d107579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro236 q selected
    | true =>
      simp only [d10742, d107579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10743 q = 0) : d107580 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10743, d107580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10743, d107580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10744 q = 0) : d107581 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10744, d107581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10744, d107581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10649 q = 0) : d107486 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, d107486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro206 q selected
    | true =>
      simp only [d10649, d107486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10650 q = 0) : d107487 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d107487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10650, d107487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10651 q = 0) : d107488 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d107488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10651, d107488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10745 q = 0) : d107582 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10745, d107582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10745, d107582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d31 q = 0) : d51883 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro188 q selected
    | true =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d32 q = 0) : d51884 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d33 q = 0) : d51885 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10652 q = 0) : d107489 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10652, d107489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10652, d107489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d10746 q = 0) : d107583 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10746, d107583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10746, d107583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d10747 q = 0) : d107584 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10747, d107584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d10747, d107584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro7437 (p : Pattern) (selected : d10753 p = 0) : d107590 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10748 q = 0) : d107585 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10748, d107585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7436 q selected
    | true =>
      simp only [d10748, d107585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10749 q = 0) : d107586 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10749, d107586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10749, d107586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10655 q = 0) : d107492 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d107492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7422 q selected
    | true =>
      simp only [d10655, d107492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10656 q = 0) : d107493 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d107493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10656, d107493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10750 q = 0) : d107587 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10750, d107587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10750, d107587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10751 q = 0) : d107588 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10751, d107588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10751, d107588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10752 q = 0) : d107589 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10752, d107589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10752, d107589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10753 q = 0) : d107590 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10753, d107590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10753, d107590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7438 (p : Pattern) (selected : d10760 p = 0) : d107491 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10755 q = 0) : d107486 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10755, d107486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro241 q selected
    | true =>
      simp only [d10755, d107486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10756 q = 0) : d107487 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10756, d107487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10756, d107487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10757 q = 0) : d107488 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10757, d107488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10757, d107488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d176 q = 0) : d51883 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d176, d51883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro211 q selected
    | true =>
      simp only [d176, d51883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d177 q = 0) : d51884 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d177, d51884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d177, d51884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d178 q = 0) : d51885 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d178, d51885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d178, d51885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10758 q = 0) : d107489 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10758, d107489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10758, d107489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d179 q = 0) : d51886 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d179, d51886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d179, d51886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10759 q = 0) : d107490 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10759, d107490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10759, d107490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10760 q = 0) : d107491 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10760, d107491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10760, d107491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro7439 (p : Pattern) (selected : d10766 p = 0) : d107497 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10761 q = 0) : d107492 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10761, d107492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7438 q selected
    | true =>
      simp only [d10761, d107492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10762 q = 0) : d107493 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10762, d107493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10762, d107493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro212 q selected
    | true =>
      simp only [d182, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d183 q = 0) : d51890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d183, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10763 q = 0) : d107494 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10763, d107494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10763, d107494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10764 q = 0) : d107495 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10764, d107495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10764, d107495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10765 q = 0) : d107496 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10765, d107496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10765, d107496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10766 q = 0) : d107497 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10766, d107497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10766, d107497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7440 (p : Pattern) (selected : d10772 p = 0) : d107596 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10655 q = 0) : d107492 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d107492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7422 q selected
    | true =>
      simp only [d10655, d107492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10656 q = 0) : d107493 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d107493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10656, d107493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10769 q = 0) : d107593 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10769, d107593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10769, d107593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10770 q = 0) : d107594 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10770, d107594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10770, d107594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10771 q = 0) : d107595 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10771, d107595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10771, d107595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10772 q = 0) : d107596 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10772, d107596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10772, d107596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7441 (p : Pattern) (selected : d10778 p = 0) : d107602 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10732 q = 0) : d107569 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10732, d107569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7434 q selected
    | true =>
      simp only [d10732, d107569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro202 q selected
  have h2 (q : Pattern) (selected : d10733 q = 0) : d107570 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10733, d107570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10733, d107570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10734 q = 0) : d107571 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10734, d107571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10734, d107571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10735 q = 0) : d107572 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10735, d107572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10735, d107572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10739 q = 0) : d107576 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10739, d107576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7435 q selected
    | true =>
      simp only [d10739, d107576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro203 q selected
  have h6 (q : Pattern) (selected : d10740 q = 0) : d107577 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10740, d107577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10740, d107577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10741 q = 0) : d107578 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10741, d107578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10741, d107578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10754 q = 0) : d107591 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10754, d107591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7437 q selected
    | true =>
      simp only [d10754, d107591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7423 q selected
  have h9 (q : Pattern) (selected : d10767 q = 0) : d107498 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10767, d107498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7439 q selected
    | true =>
      simp only [d10767, d107498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro213 q selected
  have h10 (q : Pattern) (selected : d10768 q = 0) : d107592 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10768, d107592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10768, d107592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10773 q = 0) : d107597 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10773, d107597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7440 q selected
    | true =>
      simp only [d10773, d107597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d10774 q = 0) : d107598 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10774, d107598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d10774, d107598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d10775 q = 0) : d107599 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10775, d107599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d10775, d107599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d10776 q = 0) : d107600 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10776, d107600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10776, d107600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d10777 q = 0) : d107601 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10777, d107601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10777, d107601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d10778 q = 0) : d107602 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10778, d107602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10778, d107602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro7442 (p : Pattern) (selected : d10779 p = 0) : d107603 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10655 q = 0) : d107492 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d107492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7422 q selected
    | true =>
      simp only [d10655, d107492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10656 q = 0) : d107493 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d107493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10656, d107493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d37 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro189 q selected
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d38 q = 0) : d51890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10657 q = 0) : d107494 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d107494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10657, d107494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10658 q = 0) : d107495 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10658, d107495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10658, d107495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10730 q = 0) : d107567 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10730, d107567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10730, d107567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10779 q = 0) : d107603 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10779, d107603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10779, d107603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7443 (p : Pattern) (selected : d10784 p = 0) : d107608 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10655 q = 0) : d107492 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d107492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7422 q selected
    | true =>
      simp only [d10655, d107492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10656 q = 0) : d107493 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d107493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10656, d107493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d37 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro189 q selected
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d38 q = 0) : d51890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10657 q = 0) : d107494 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d107494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10657, d107494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10736 q = 0) : d107573 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10736, d107573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10736, d107573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10737 q = 0) : d107574 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10737, d107574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10737, d107574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10784 q = 0) : d107608 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10784, d107608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10784, d107608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7444 (p : Pattern) (selected : d10788 p = 0) : d107612 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10748 q = 0) : d107585 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10748, d107585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7436 q selected
    | true =>
      simp only [d10748, d107585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10749 q = 0) : d107586 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10749, d107586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10749, d107586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10655 q = 0) : d107492 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d107492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7422 q selected
    | true =>
      simp only [d10655, d107492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10656 q = 0) : d107493 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d107493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10656, d107493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10750 q = 0) : d107587 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10750, d107587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10750, d107587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10751 q = 0) : d107588 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10751, d107588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10751, d107588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10752 q = 0) : d107589 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10752, d107589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10752, d107589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10788 q = 0) : d107612 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10788, d107612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10788, d107612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7445 (p : Pattern) (selected : d10790 p = 0) : d107504 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10761 q = 0) : d107492 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10761, d107492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7438 q selected
    | true =>
      simp only [d10761, d107492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10762 q = 0) : d107493 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10762, d107493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10762, d107493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d182 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro212 q selected
    | true =>
      simp only [d182, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d183 q = 0) : d51890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d183, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10763 q = 0) : d107494 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10763, d107494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10763, d107494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10764 q = 0) : d107495 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10764, d107495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10764, d107495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10765 q = 0) : d107496 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10765, d107496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10765, d107496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10790 q = 0) : d107504 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10790, d107504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10790, d107504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7446 (p : Pattern) (selected : d10793 p = 0) : d107615 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10655 q = 0) : d107492 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d107492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7422 q selected
    | true =>
      simp only [d10655, d107492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10656 q = 0) : d107493 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d107493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10656, d107493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10769 q = 0) : d107593 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10769, d107593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10769, d107593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10770 q = 0) : d107594 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10770, d107594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10770, d107594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10771 q = 0) : d107595 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10771, d107595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10771, d107595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10793 q = 0) : d107615 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10793, d107615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10793, d107615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7447 (p : Pattern) (selected : d10799 p = 0) : d107621 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10732 q = 0) : d107569 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10732, d107569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7434 q selected
    | true =>
      simp only [d10732, d107569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro202 q selected
  have h2 (q : Pattern) (selected : d10733 q = 0) : d107570 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10733, d107570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10733, d107570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10734 q = 0) : d107571 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10734, d107571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10734, d107571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10735 q = 0) : d107572 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10735, d107572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10735, d107572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10739 q = 0) : d107576 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10739, d107576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7435 q selected
    | true =>
      simp only [d10739, d107576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro203 q selected
  have h6 (q : Pattern) (selected : d10740 q = 0) : d107577 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10740, d107577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10740, d107577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10741 q = 0) : d107578 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10741, d107578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10741, d107578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10754 q = 0) : d107591 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10754, d107591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7437 q selected
    | true =>
      simp only [d10754, d107591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7423 q selected
  have h9 (q : Pattern) (selected : d10767 q = 0) : d107498 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10767, d107498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7439 q selected
    | true =>
      simp only [d10767, d107498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro213 q selected
  have h10 (q : Pattern) (selected : d10768 q = 0) : d107592 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10768, d107592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10768, d107592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10773 q = 0) : d107597 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10773, d107597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7440 q selected
    | true =>
      simp only [d10773, d107597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d10774 q = 0) : d107598 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10774, d107598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d10774, d107598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d10775 q = 0) : d107599 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10775, d107599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d10775, d107599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d10776 q = 0) : d107600 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10776, d107600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10776, d107600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d10777 q = 0) : d107601 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10777, d107601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10777, d107601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d10780 q = 0) : d107604 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10780, d107604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7442 q selected
    | true =>
      simp only [d10780, d107604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro215 q selected
  have h17 (q : Pattern) (selected : d10781 q = 0) : d107605 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10781, d107605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10781, d107605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d10782 q = 0) : d107606 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10782, d107606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d10782, d107606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d10783 q = 0) : d107607 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10783, d107607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10783, d107607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d10785 q = 0) : d107609 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10785, d107609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7443 q selected
    | true =>
      simp only [d10785, d107609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro216 q selected
  have h21 (q : Pattern) (selected : d10786 q = 0) : d107610 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10786, d107610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10786, d107610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d10787 q = 0) : d107611 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10787, d107611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d10787, d107611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d10789 q = 0) : d107613 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10789, d107613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7444 q selected
    | true =>
      simp only [d10789, d107613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7425 q selected
  have h24 (q : Pattern) (selected : d10791 q = 0) : d107505 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10791, d107505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7445 q selected
    | true =>
      simp only [d10791, d107505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro218 q selected
  have h25 (q : Pattern) (selected : d10792 q = 0) : d107614 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10792, d107614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d10792, d107614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d10794 q = 0) : d107616 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10794, d107616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7446 q selected
    | true =>
      simp only [d10794, d107616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d10795 q = 0) : d107617 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10795, d107617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d10795, d107617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d10796 q = 0) : d107618 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10796, d107618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d10796, d107618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d10797 q = 0) : d107619 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10797, d107619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d10797, d107619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d10798 q = 0) : d107620 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10798, d107620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d10798, d107620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d10799 q = 0) : d107621 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10799, d107621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d10799, d107621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro7448 (p : Pattern) (selected : d10801 p = 0) : d107623 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10661 q = 0) : d107498 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d107498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7423 q selected
    | true =>
      simp only [d10661, d107498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
  have h2 (q : Pattern) (selected : d10715 q = 0) : d107552 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10715, d107552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10715, d107552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10716 q = 0) : d107553 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10716, d107553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10716, d107553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10717 q = 0) : d107554 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10717, d107554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10717, d107554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10718 q = 0) : d107555 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10718, d107555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10718, d107555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d43 q = 0) : d51895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d100 q = 0) : d51952 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d51952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d100, d51952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d101 q = 0) : d51953 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d51953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d101, d51953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d102 q = 0) : d51954 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d51954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d102, d51954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d103 q = 0) : d51955 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d51955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d103, d51955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10801 q = 0) : d107623 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10801, d107623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10801, d107623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro7449 (p : Pattern) (selected : d10808 p = 0) : d107630 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10789 q = 0) : d107613 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10789, d107613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7444 q selected
    | true =>
      simp only [d10789, d107613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7425 q selected
  have h2 (q : Pattern) (selected : d10791 q = 0) : d107505 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10791, d107505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7445 q selected
    | true =>
      simp only [d10791, d107505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro218 q selected
  have h3 (q : Pattern) (selected : d10792 q = 0) : d107614 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10792, d107614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10792, d107614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10794 q = 0) : d107616 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10794, d107616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7446 q selected
    | true =>
      simp only [d10794, d107616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10795 q = 0) : d107617 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10795, d107617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10795, d107617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10796 q = 0) : d107618 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10796, d107618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10796, d107618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10806 q = 0) : d107628 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10806, d107628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10806, d107628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10807 q = 0) : d107629 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10807, d107629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10807, d107629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10808 q = 0) : d107630 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10808, d107630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10808, d107630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7450 (p : Pattern) (selected : d10819 p = 0) : d107641 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10814 q = 0) : d107636 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10814, d107636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro253 q selected
    | true =>
      simp only [d10814, d107636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10815 q = 0) : d107637 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10815, d107637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10815, d107637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10816 q = 0) : d107638 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10816, d107638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10816, d107638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10686 q = 0) : d107523 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, d107523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro222 q selected
    | true =>
      simp only [d10686, d107523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10687 q = 0) : d107524 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d107524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10687, d107524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10688 q = 0) : d107525 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d107525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10688, d107525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10817 q = 0) : d107639 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10817, d107639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10817, d107639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
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
  have h11 (q : Pattern) (selected : d10689 q = 0) : d107526 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10689, d107526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10689, d107526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d10818 q = 0) : d107640 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10818, d107640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10818, d107640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d10819 q = 0) : d107641 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10819, d107641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d10819, d107641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro7451 (p : Pattern) (selected : d10825 p = 0) : d107647 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10820 q = 0) : d107642 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10820, d107642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7450 q selected
    | true =>
      simp only [d10820, d107642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10821 q = 0) : d107643 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10821, d107643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10821, d107643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10692 q = 0) : d107529 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10692, d107529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7428 q selected
    | true =>
      simp only [d10692, d107529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10693 q = 0) : d107530 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10693, d107530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10693, d107530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10822 q = 0) : d107644 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10822, d107644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10822, d107644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10823 q = 0) : d107645 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10823, d107645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10823, d107645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10824 q = 0) : d107646 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10824, d107646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10824, d107646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10825 q = 0) : d107647 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10825, d107647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10825, d107647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7452 (p : Pattern) (selected : d10832 p = 0) : d107528 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10827 q = 0) : d107523 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10827, d107523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro256 q selected
    | true =>
      simp only [d10827, d107523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10828 q = 0) : d107524 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10828, d107524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10828, d107524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10829 q = 0) : d107525 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10829, d107525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10829, d107525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
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
  have h7 (q : Pattern) (selected : d10830 q = 0) : d107526 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10830, d107526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10830, d107526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
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
  have h9 (q : Pattern) (selected : d10831 q = 0) : d107527 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10831, d107527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10831, d107527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10832 q = 0) : d107528 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10832, d107528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10832, d107528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro7453 (p : Pattern) (selected : d10838 p = 0) : d107534 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10833 q = 0) : d107529 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10833, d107529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7452 q selected
    | true =>
      simp only [d10833, d107529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10834 q = 0) : d107530 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10834, d107530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10834, d107530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d257 q = 0) : d51930 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d257, d51930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro226 q selected
    | true =>
      simp only [d257, d51930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d258 q = 0) : d51931 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d258, d51931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d258, d51931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10835 q = 0) : d107531 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10835, d107531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10835, d107531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10836 q = 0) : d107532 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10836, d107532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10836, d107532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10837 q = 0) : d107533 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10837, d107533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10837, d107533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10838 q = 0) : d107534 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10838, d107534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10838, d107534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7454 (p : Pattern) (selected : d10844 p = 0) : d107653 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10692 q = 0) : d107529 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10692, d107529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7428 q selected
    | true =>
      simp only [d10692, d107529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10693 q = 0) : d107530 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10693, d107530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10693, d107530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10841 q = 0) : d107650 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10841, d107650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10841, d107650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10842 q = 0) : d107651 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10842, d107651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10842, d107651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10843 q = 0) : d107652 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10843, d107652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10843, d107652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10844 q = 0) : d107653 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10844, d107653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10844, d107653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7455 (p : Pattern) (selected : d10850 p = 0) : d107659 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10826 q = 0) : d107648 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10826, d107648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7451 q selected
    | true =>
      simp only [d10826, d107648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7429 q selected
  have h2 (q : Pattern) (selected : d10839 q = 0) : d107535 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10839, d107535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7453 q selected
    | true =>
      simp only [d10839, d107535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro227 q selected
  have h3 (q : Pattern) (selected : d10840 q = 0) : d107649 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10840, d107649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10840, d107649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10845 q = 0) : d107654 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10845, d107654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7454 q selected
    | true =>
      simp only [d10845, d107654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10846 q = 0) : d107655 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10846, d107655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10846, d107655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10847 q = 0) : d107656 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10847, d107656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10847, d107656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10848 q = 0) : d107657 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10848, d107657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10848, d107657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10849 q = 0) : d107658 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10849, d107658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10849, d107658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10850 q = 0) : d107659 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10850, d107659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10850, d107659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7456 (p : Pattern) (selected : d10856 p = 0) : d107665 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10720 q = 0) : d107557 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10720, d107557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10720, d107557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7432 q selected
  have h2 (q : Pattern) (selected : d10721 q = 0) : d107558 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10721, d107558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10721, d107558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d10727 q = 0) : d107564 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10727, d107564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7432 q selected
    | true =>
      simp only [d10727, d107564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7433 q selected
  have h4 (q : Pattern) (selected : d10728 q = 0) : d107565 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10728, d107565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10728, d107565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10729 q = 0) : d107566 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d10729, d107566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10729, d107566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10800 q = 0) : d107622 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10800, d107622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7441 q selected
    | true =>
      simp only [d10800, d107622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7447 q selected
  have h7 (q : Pattern) (selected : d10802 q = 0) : d107624 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10802, d107624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7448 q selected
    | true =>
      simp only [d10802, d107624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro201 q selected
  have h8 (q : Pattern) (selected : d10803 q = 0) : d107625 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10803, d107625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10803, d107625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10804 q = 0) : d107626 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d10804, d107626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10804, d107626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d10805 q = 0) : d107627 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d10805, d107627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10805, d107627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10809 q = 0) : d107631 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10809, d107631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10809, d107631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7449 q selected
  have h12 (q : Pattern) (selected : d407 q = 0) : d52173 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d52173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d407, d52173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro252 q selected
  have h13 (q : Pattern) (selected : d10810 q = 0) : d107632 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10810, d107632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d10810, d107632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d10811 q = 0) : d107633 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d10811, d107633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d10811, d107633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d10812 q = 0) : d107634 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d10812, d107634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d10812, d107634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d10813 q = 0) : d107635 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d10813, d107635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d10813, d107635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d10851 q = 0) : d107660 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10851, d107660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10851, d107660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7455 q selected
  have h18 (q : Pattern) (selected : d463 q = 0) : d52210 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d52210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d463, d52210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro260 q selected
  have h19 (q : Pattern) (selected : d10852 q = 0) : d107661 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10852, d107661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d10852, d107661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d10853 q = 0) : d107662 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d10853, d107662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d10853, d107662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d10854 q = 0) : d107663 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d10854, d107663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d10854, d107663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d10855 q = 0) : d107664 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d10855, d107664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d10855, d107664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d10856 q = 0) : d107665 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d10856, d107665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d10856, d107665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro7457 (p : Pattern) (selected : d10862 p = 0) : d107671 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d96 q = 0) : d51948 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, d51948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96, d51948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro199 q selected
  have h2 (q : Pattern) (selected : d97 q = 0) : d51949 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, d51949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d97, d51949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d98 q = 0) : d51950 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, d51950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d98, d51950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d99 q = 0) : d51951 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, d51951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99, d51951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10710 q = 0) : d107547 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d10710, d107547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10710, d107547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7431 q selected
  have h6 (q : Pattern) (selected : d10711 q = 0) : d107548 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d10711, d107548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10711, d107548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10712 q = 0) : d107549 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d10712, d107549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10712, d107549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10713 q = 0) : d107550 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d10713, d107550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10713, d107550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d10714 q = 0) : d107551 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d10714, d107551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10714, d107551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10857 q = 0) : d107666 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d10857, d107666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10857, d107666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7456 q selected
  have h11 (q : Pattern) (selected : d10858 q = 0) : d107667 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d10858, d107667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10858, d107667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d10859 q = 0) : d107668 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d10859, d107668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10859, d107668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d10860 q = 0) : d107669 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d10860, d107669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10860, d107669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d10861 q = 0) : d107670 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d10861, d107670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10861, d107670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d10862 q = 0) : d107671 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d10862, d107671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10862, d107671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro7458 (p : Pattern) (selected : d10865 p = 0) : d107674 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10742 q = 0) : d107579 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10742, d107579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro236 q selected
    | true =>
      simp only [d10742, d107579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10743 q = 0) : d107580 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10743, d107580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10743, d107580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10744 q = 0) : d107581 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10744, d107581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10744, d107581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10649 q = 0) : d107486 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, d107486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro206 q selected
    | true =>
      simp only [d10649, d107486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10650 q = 0) : d107487 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d107487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10650, d107487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10651 q = 0) : d107488 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d107488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10651, d107488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10745 q = 0) : d107582 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10745, d107582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10745, d107582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10863 q = 0) : d107672 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10863, d107672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10863, d107672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10864 q = 0) : d107673 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10864, d107673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10864, d107673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10865 q = 0) : d107674 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10865, d107674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10865, d107674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro7459 (p : Pattern) (selected : d10869 p = 0) : d107678 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10649 q = 0) : d107486 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, d107486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro206 q selected
    | true =>
      simp only [d10649, d107486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10650 q = 0) : d107487 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d107487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10650, d107487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10651 q = 0) : d107488 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d107488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10651, d107488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10863 q = 0) : d107672 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10863, d107672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10863, d107672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10868 q = 0) : d107677 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10868, d107677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10868, d107677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10869 q = 0) : d107678 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10869, d107678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10869, d107678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7460 (p : Pattern) (selected : d10875 p = 0) : d107684 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10866 q = 0) : d107675 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d107675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7458 q selected
    | true =>
      simp only [d10866, d107675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10867 q = 0) : d107676 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d107676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10867, d107676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10870 q = 0) : d107679 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7459 q selected
    | true =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10871 q = 0) : d107680 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10872 q = 0) : d107681 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d107681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10872, d107681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10873 q = 0) : d107682 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10873, d107682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10873, d107682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10874 q = 0) : d107683 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10874, d107683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10874, d107683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10875 q = 0) : d107684 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10875, d107684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10875, d107684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7461 (p : Pattern) (selected : d10879 p = 0) : d107688 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10870 q = 0) : d107679 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7459 q selected
    | true =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10871 q = 0) : d107680 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10876 q = 0) : d107685 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d107685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10876, d107685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10877 q = 0) : d107686 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10877, d107686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10877, d107686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10878 q = 0) : d107687 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10878, d107687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10878, d107687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10879 q = 0) : d107688 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10879, d107688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10879, d107688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7462 (p : Pattern) (selected : d10885 p = 0) : d107694 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10880 q = 0) : d107689 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10880, d107689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7460 q selected
    | true =>
      simp only [d10880, d107689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7461 q selected
  have h2 (q : Pattern) (selected : d10881 q = 0) : d107690 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10881, d107690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10881, d107690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10882 q = 0) : d107691 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10882, d107691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10882, d107691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10883 q = 0) : d107692 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10883, d107692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10883, d107692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10884 q = 0) : d107693 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10884, d107693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10884, d107693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10885 q = 0) : d107694 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10885, d107694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10885, d107694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7463 (p : Pattern) (selected : d10888 p = 0) : d107697 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10866 q = 0) : d107675 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d107675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7458 q selected
    | true =>
      simp only [d10866, d107675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10867 q = 0) : d107676 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d107676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10867, d107676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10870 q = 0) : d107679 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7459 q selected
    | true =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10871 q = 0) : d107680 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10872 q = 0) : d107681 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d107681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10872, d107681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10873 q = 0) : d107682 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10873, d107682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10873, d107682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10874 q = 0) : d107683 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10874, d107683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10874, d107683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10888 q = 0) : d107697 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10888, d107697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10888, d107697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7464 (p : Pattern) (selected : d10889 p = 0) : d107698 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10870 q = 0) : d107679 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7459 q selected
    | true =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10871 q = 0) : d107680 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10876 q = 0) : d107685 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d107685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10876, d107685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10877 q = 0) : d107686 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10877, d107686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10877, d107686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10878 q = 0) : d107687 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10878, d107687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10878, d107687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10889 q = 0) : d107698 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10889, d107698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10889, d107698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7465 (p : Pattern) (selected : d10895 p = 0) : d107704 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10880 q = 0) : d107689 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10880, d107689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7460 q selected
    | true =>
      simp only [d10880, d107689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7461 q selected
  have h2 (q : Pattern) (selected : d10881 q = 0) : d107690 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10881, d107690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10881, d107690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10882 q = 0) : d107691 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10882, d107691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10882, d107691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10883 q = 0) : d107692 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10883, d107692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10883, d107692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10884 q = 0) : d107693 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10884, d107693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10884, d107693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10890 q = 0) : d107699 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10890, d107699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7463 q selected
    | true =>
      simp only [d10890, d107699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7464 q selected
  have h7 (q : Pattern) (selected : d10891 q = 0) : d107700 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10891, d107700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10891, d107700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10892 q = 0) : d107701 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10892, d107701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10892, d107701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10893 q = 0) : d107702 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10893, d107702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10893, d107702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10894 q = 0) : d107703 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10894, d107703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10894, d107703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10895 q = 0) : d107704 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10895, d107704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10895, d107704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro7466 (p : Pattern) (selected : d10900 p = 0) : d107709 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10866 q = 0) : d107675 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d107675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7458 q selected
    | true =>
      simp only [d10866, d107675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10867 q = 0) : d107676 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d107676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10867, d107676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10870 q = 0) : d107679 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7459 q selected
    | true =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10871 q = 0) : d107680 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10872 q = 0) : d107681 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d107681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10872, d107681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10873 q = 0) : d107682 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10873, d107682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10873, d107682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10899 q = 0) : d107708 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10899, d107708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10899, d107708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10900 q = 0) : d107709 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10900, d107709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10900, d107709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7467 (p : Pattern) (selected : d10902 p = 0) : d107711 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10870 q = 0) : d107679 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7459 q selected
    | true =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10871 q = 0) : d107680 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10876 q = 0) : d107685 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d107685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10876, d107685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10877 q = 0) : d107686 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10877, d107686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10877, d107686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10901 q = 0) : d107710 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10901, d107710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10901, d107710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10902 q = 0) : d107711 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10902, d107711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10902, d107711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7468 (p : Pattern) (selected : d10909 p = 0) : d107718 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10866 q = 0) : d107675 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d107675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7458 q selected
    | true =>
      simp only [d10866, d107675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10867 q = 0) : d107676 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d107676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10867, d107676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10870 q = 0) : d107679 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7459 q selected
    | true =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10871 q = 0) : d107680 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10872 q = 0) : d107681 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d107681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10872, d107681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10907 q = 0) : d107716 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10907, d107716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10907, d107716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10908 q = 0) : d107717 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10908, d107717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10908, d107717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10909 q = 0) : d107718 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10909, d107718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10909, d107718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7469 (p : Pattern) (selected : d10912 p = 0) : d107721 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10870 q = 0) : d107679 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7459 q selected
    | true =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10871 q = 0) : d107680 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10876 q = 0) : d107685 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d107685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10876, d107685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10910 q = 0) : d107719 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10910, d107719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10910, d107719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10911 q = 0) : d107720 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10911, d107720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10911, d107720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10912 q = 0) : d107721 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10912, d107721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10912, d107721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7470 (p : Pattern) (selected : d10921 p = 0) : d107730 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10916 q = 0) : d107725 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10916, d107725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro278 q selected
    | true =>
      simp only [d10916, d107725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10917 q = 0) : d107726 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10917, d107726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10917, d107726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10918 q = 0) : d107727 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10918, d107727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10918, d107727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10742 q = 0) : d107579 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10742, d107579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro236 q selected
    | true =>
      simp only [d10742, d107579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10743 q = 0) : d107580 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10743, d107580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10743, d107580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10744 q = 0) : d107581 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10744, d107581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10744, d107581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10919 q = 0) : d107728 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10919, d107728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10919, d107728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10649 q = 0) : d107486 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, d107486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro206 q selected
    | true =>
      simp only [d10649, d107486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10650 q = 0) : d107487 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d107487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10650, d107487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10651 q = 0) : d107488 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d107488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10651, d107488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10745 q = 0) : d107582 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10745, d107582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10745, d107582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d10920 q = 0) : d107729 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10920, d107729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10920, d107729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d10921 q = 0) : d107730 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10921, d107730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d10921, d107730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro7471 (p : Pattern) (selected : d10927 p = 0) : d107736 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10922 q = 0) : d107731 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10922, d107731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7470 q selected
    | true =>
      simp only [d10922, d107731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10923 q = 0) : d107732 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10923, d107732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10923, d107732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10866 q = 0) : d107675 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d107675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7458 q selected
    | true =>
      simp only [d10866, d107675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10867 q = 0) : d107676 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d107676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10867, d107676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10924 q = 0) : d107733 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10924, d107733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10924, d107733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10925 q = 0) : d107734 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10925, d107734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10925, d107734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10926 q = 0) : d107735 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10926, d107735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10926, d107735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10927 q = 0) : d107736 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10927, d107736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10927, d107736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7472 (p : Pattern) (selected : d10935 p = 0) : d107674 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10929 q = 0) : d107579 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10929, d107579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro283 q selected
    | true =>
      simp only [d10929, d107579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10930 q = 0) : d107580 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10930, d107580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10930, d107580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10931 q = 0) : d107581 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10931, d107581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10931, d107581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10755 q = 0) : d107486 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10755, d107486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro241 q selected
    | true =>
      simp only [d10755, d107486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10756 q = 0) : d107487 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10756, d107487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10756, d107487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10757 q = 0) : d107488 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10757, d107488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10757, d107488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10932 q = 0) : d107582 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10932, d107582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10932, d107582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10933 q = 0) : d107672 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10933, d107672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10933, d107672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10934 q = 0) : d107673 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10934, d107673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10934, d107673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10935 q = 0) : d107674 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10935, d107674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d10935, d107674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro7473 (p : Pattern) (selected : d10939 p = 0) : d107678 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10755 q = 0) : d107486 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10755, d107486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro241 q selected
    | true =>
      simp only [d10755, d107486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10756 q = 0) : d107487 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10756, d107487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10756, d107487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10757 q = 0) : d107488 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10757, d107488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10757, d107488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10933 q = 0) : d107672 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10933, d107672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10933, d107672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10938 q = 0) : d107677 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10938, d107677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10938, d107677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10939 q = 0) : d107678 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10939, d107678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10939, d107678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7474 (p : Pattern) (selected : d10945 p = 0) : d107684 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10936 q = 0) : d107675 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10936, d107675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7472 q selected
    | true =>
      simp only [d10936, d107675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10937 q = 0) : d107676 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10937, d107676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10937, d107676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10940 q = 0) : d107679 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10940, d107679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7473 q selected
    | true =>
      simp only [d10940, d107679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10941 q = 0) : d107680 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10941, d107680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10941, d107680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10942 q = 0) : d107681 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10942, d107681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10942, d107681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10943 q = 0) : d107682 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10943, d107682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10943, d107682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10944 q = 0) : d107683 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10944, d107683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10944, d107683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10945 q = 0) : d107684 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10945, d107684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10945, d107684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro7475 (p : Pattern) (selected : d10949 p = 0) : d107688 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10940 q = 0) : d107679 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10940, d107679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7473 q selected
    | true =>
      simp only [d10940, d107679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10941 q = 0) : d107680 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10941, d107680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10941, d107680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10946 q = 0) : d107685 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10946, d107685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10946, d107685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10947 q = 0) : d107686 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10947, d107686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10947, d107686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10948 q = 0) : d107687 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10948, d107687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10948, d107687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10949 q = 0) : d107688 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10949, d107688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10949, d107688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7476 (p : Pattern) (selected : d10955 p = 0) : d107742 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10866 q = 0) : d107675 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d107675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7458 q selected
    | true =>
      simp only [d10866, d107675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10867 q = 0) : d107676 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d107676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10867, d107676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10952 q = 0) : d107739 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10952, d107739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10952, d107739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10953 q = 0) : d107740 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10953, d107740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10953, d107740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10954 q = 0) : d107741 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10954, d107741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10954, d107741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10955 q = 0) : d107742 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10955, d107742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10955, d107742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7477 (p : Pattern) (selected : d10961 p = 0) : d107748 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10903 q = 0) : d107712 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10903, d107712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7466 q selected
    | true =>
      simp only [d10903, d107712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7467 q selected
  have h2 (q : Pattern) (selected : d10904 q = 0) : d107713 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10904, d107713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10904, d107713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10905 q = 0) : d107714 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10905, d107714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10905, d107714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10906 q = 0) : d107715 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10906, d107715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10906, d107715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10913 q = 0) : d107722 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10913, d107722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7468 q selected
    | true =>
      simp only [d10913, d107722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7469 q selected
  have h6 (q : Pattern) (selected : d10914 q = 0) : d107723 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10914, d107723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10914, d107723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10915 q = 0) : d107724 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10915, d107724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10915, d107724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10928 q = 0) : d107737 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10928, d107737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7471 q selected
    | true =>
      simp only [d10928, d107737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7460 q selected
  have h9 (q : Pattern) (selected : d10950 q = 0) : d107689 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10950, d107689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7474 q selected
    | true =>
      simp only [d10950, d107689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7475 q selected
  have h10 (q : Pattern) (selected : d10951 q = 0) : d107738 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10951, d107738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10951, d107738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10956 q = 0) : d107743 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10956, d107743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7476 q selected
    | true =>
      simp only [d10956, d107743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d10957 q = 0) : d107744 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10957, d107744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d10957, d107744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d10958 q = 0) : d107745 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10958, d107745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d10958, d107745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d10959 q = 0) : d107746 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10959, d107746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10959, d107746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d10960 q = 0) : d107747 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10960, d107747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10960, d107747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d10961 q = 0) : d107748 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10961, d107748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10961, d107748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro7478 (p : Pattern) (selected : d10962 p = 0) : d107749 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10866 q = 0) : d107675 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d107675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7458 q selected
    | true =>
      simp only [d10866, d107675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10867 q = 0) : d107676 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d107676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10867, d107676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10870 q = 0) : d107679 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7459 q selected
    | true =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10871 q = 0) : d107680 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10872 q = 0) : d107681 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d107681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10872, d107681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10873 q = 0) : d107682 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10873, d107682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10873, d107682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10899 q = 0) : d107708 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10899, d107708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10899, d107708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10962 q = 0) : d107749 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10962, d107749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10962, d107749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7479 (p : Pattern) (selected : d10963 p = 0) : d107750 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10870 q = 0) : d107679 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7459 q selected
    | true =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10871 q = 0) : d107680 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10876 q = 0) : d107685 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d107685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10876, d107685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10877 q = 0) : d107686 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10877, d107686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10877, d107686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10901 q = 0) : d107710 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10901, d107710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10901, d107710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10963 q = 0) : d107750 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10963, d107750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10963, d107750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7480 (p : Pattern) (selected : d10968 p = 0) : d107755 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10866 q = 0) : d107675 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d107675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7458 q selected
    | true =>
      simp only [d10866, d107675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10867 q = 0) : d107676 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d107676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10867, d107676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10870 q = 0) : d107679 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7459 q selected
    | true =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10871 q = 0) : d107680 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10872 q = 0) : d107681 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d107681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10872, d107681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10907 q = 0) : d107716 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10907, d107716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10907, d107716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10908 q = 0) : d107717 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10908, d107717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10908, d107717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10968 q = 0) : d107755 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10968, d107755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10968, d107755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7481 (p : Pattern) (selected : d10969 p = 0) : d107756 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10870 q = 0) : d107679 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7459 q selected
    | true =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10871 q = 0) : d107680 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10876 q = 0) : d107685 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d107685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10876, d107685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10910 q = 0) : d107719 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10910, d107719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10910, d107719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10911 q = 0) : d107720 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10911, d107720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10911, d107720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10969 q = 0) : d107756 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10969, d107756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10969, d107756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7482 (p : Pattern) (selected : d10973 p = 0) : d107760 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10922 q = 0) : d107731 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10922, d107731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7470 q selected
    | true =>
      simp only [d10922, d107731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10923 q = 0) : d107732 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10923, d107732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10923, d107732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10866 q = 0) : d107675 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d107675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7458 q selected
    | true =>
      simp only [d10866, d107675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10867 q = 0) : d107676 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d107676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10867, d107676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10924 q = 0) : d107733 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10924, d107733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10924, d107733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10925 q = 0) : d107734 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10925, d107734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10925, d107734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10926 q = 0) : d107735 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10926, d107735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10926, d107735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10973 q = 0) : d107760 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10973, d107760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10973, d107760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7483 (p : Pattern) (selected : d10975 p = 0) : d107697 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10936 q = 0) : d107675 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10936, d107675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7472 q selected
    | true =>
      simp only [d10936, d107675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10937 q = 0) : d107676 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10937, d107676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10937, d107676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10940 q = 0) : d107679 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10940, d107679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7473 q selected
    | true =>
      simp only [d10940, d107679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10941 q = 0) : d107680 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10941, d107680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10941, d107680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10942 q = 0) : d107681 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10942, d107681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10942, d107681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10943 q = 0) : d107682 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10943, d107682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10943, d107682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10944 q = 0) : d107683 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10944, d107683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10944, d107683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10975 q = 0) : d107697 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10975, d107697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10975, d107697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7484 (p : Pattern) (selected : d10976 p = 0) : d107698 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10940 q = 0) : d107679 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10940, d107679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7473 q selected
    | true =>
      simp only [d10940, d107679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10941 q = 0) : d107680 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10941, d107680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10941, d107680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10946 q = 0) : d107685 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10946, d107685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10946, d107685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10947 q = 0) : d107686 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10947, d107686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10947, d107686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10948 q = 0) : d107687 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10948, d107687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10948, d107687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10976 q = 0) : d107698 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10976, d107698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10976, d107698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7485 (p : Pattern) (selected : d10979 p = 0) : d107763 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10866 q = 0) : d107675 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d107675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7458 q selected
    | true =>
      simp only [d10866, d107675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10867 q = 0) : d107676 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d107676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10867, d107676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10952 q = 0) : d107739 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10952, d107739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10952, d107739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10953 q = 0) : d107740 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10953, d107740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10953, d107740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10954 q = 0) : d107741 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10954, d107741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10954, d107741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10979 q = 0) : d107763 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10979, d107763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10979, d107763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7486 (p : Pattern) (selected : d10985 p = 0) : d107769 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10903 q = 0) : d107712 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10903, d107712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7466 q selected
    | true =>
      simp only [d10903, d107712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7467 q selected
  have h2 (q : Pattern) (selected : d10904 q = 0) : d107713 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10904, d107713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10904, d107713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10905 q = 0) : d107714 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10905, d107714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10905, d107714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10906 q = 0) : d107715 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10906, d107715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10906, d107715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10913 q = 0) : d107722 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10913, d107722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7468 q selected
    | true =>
      simp only [d10913, d107722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7469 q selected
  have h6 (q : Pattern) (selected : d10914 q = 0) : d107723 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10914, d107723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10914, d107723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10915 q = 0) : d107724 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10915, d107724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10915, d107724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d10928 q = 0) : d107737 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10928, d107737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7471 q selected
    | true =>
      simp only [d10928, d107737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7460 q selected
  have h9 (q : Pattern) (selected : d10950 q = 0) : d107689 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10950, d107689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7474 q selected
    | true =>
      simp only [d10950, d107689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7475 q selected
  have h10 (q : Pattern) (selected : d10951 q = 0) : d107738 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10951, d107738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d10951, d107738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10956 q = 0) : d107743 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10956, d107743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7476 q selected
    | true =>
      simp only [d10956, d107743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d10957 q = 0) : d107744 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10957, d107744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d10957, d107744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d10958 q = 0) : d107745 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10958, d107745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d10958, d107745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d10959 q = 0) : d107746 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10959, d107746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10959, d107746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d10960 q = 0) : d107747 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10960, d107747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10960, d107747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d10964 q = 0) : d107751 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10964, d107751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7478 q selected
    | true =>
      simp only [d10964, d107751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7479 q selected
  have h17 (q : Pattern) (selected : d10965 q = 0) : d107752 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10965, d107752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10965, d107752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d10966 q = 0) : d107753 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10966, d107753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d10966, d107753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d10967 q = 0) : d107754 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10967, d107754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10967, d107754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d10970 q = 0) : d107757 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10970, d107757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7480 q selected
    | true =>
      simp only [d10970, d107757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7481 q selected
  have h21 (q : Pattern) (selected : d10971 q = 0) : d107758 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10971, d107758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10971, d107758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d10972 q = 0) : d107759 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10972, d107759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d10972, d107759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d10974 q = 0) : d107761 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10974, d107761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7482 q selected
    | true =>
      simp only [d10974, d107761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7463 q selected
  have h24 (q : Pattern) (selected : d10977 q = 0) : d107699 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10977, d107699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7483 q selected
    | true =>
      simp only [d10977, d107699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7484 q selected
  have h25 (q : Pattern) (selected : d10978 q = 0) : d107762 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10978, d107762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d10978, d107762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d10980 q = 0) : d107764 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10980, d107764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7485 q selected
    | true =>
      simp only [d10980, d107764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d10981 q = 0) : d107765 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10981, d107765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d10981, d107765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d10982 q = 0) : d107766 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10982, d107766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d10982, d107766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d10983 q = 0) : d107767 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10983, d107767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d10983, d107767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d10984 q = 0) : d107768 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10984, d107768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d10984, d107768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d10985 q = 0) : d107769 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10985, d107769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d10985, d107769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro7487 (p : Pattern) (selected : d10992 p = 0) : d107776 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10880 q = 0) : d107689 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10880, d107689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7460 q selected
    | true =>
      simp only [d10880, d107689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7461 q selected
  have h2 (q : Pattern) (selected : d10881 q = 0) : d107690 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10881, d107690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10881, d107690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10882 q = 0) : d107691 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10882, d107691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10882, d107691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10883 q = 0) : d107692 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10883, d107692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10883, d107692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10884 q = 0) : d107693 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10884, d107693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10884, d107693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10987 q = 0) : d107771 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10987, d107771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7461 q selected
    | true =>
      simp only [d10987, d107771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10988 q = 0) : d107772 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10988, d107772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10988, d107772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10989 q = 0) : d107773 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10989, d107773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10989, d107773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10990 q = 0) : d107774 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10990, d107774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10990, d107774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10991 q = 0) : d107775 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10991, d107775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10991, d107775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10992 q = 0) : d107776 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10992, d107776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10992, d107776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro7488 (p : Pattern) (selected : d10998 p = 0) : d107782 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10987 q = 0) : d107771 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10987, d107771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7461 q selected
    | true =>
      simp only [d10987, d107771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10988 q = 0) : d107772 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10988, d107772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10988, d107772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10989 q = 0) : d107773 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10989, d107773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10989, d107773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10990 q = 0) : d107774 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10990, d107774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10990, d107774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10991 q = 0) : d107775 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10991, d107775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10991, d107775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10993 q = 0) : d107777 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10993, d107777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7464 q selected
    | true =>
      simp only [d10993, d107777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d10994 q = 0) : d107778 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10994, d107778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10994, d107778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10995 q = 0) : d107779 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10995, d107779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d10995, d107779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10996 q = 0) : d107780 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10996, d107780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10996, d107780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10997 q = 0) : d107781 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10997, d107781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10997, d107781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10998 q = 0) : d107782 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10998, d107782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d10998, d107782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro7489 (p : Pattern) (selected : d11005 p = 0) : d107789 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10974 q = 0) : d107761 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10974, d107761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7482 q selected
    | true =>
      simp only [d10974, d107761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7463 q selected
  have h2 (q : Pattern) (selected : d10977 q = 0) : d107699 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10977, d107699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7483 q selected
    | true =>
      simp only [d10977, d107699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7484 q selected
  have h3 (q : Pattern) (selected : d10978 q = 0) : d107762 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10978, d107762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d10978, d107762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10980 q = 0) : d107764 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10980, d107764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7485 q selected
    | true =>
      simp only [d10980, d107764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10981 q = 0) : d107765 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10981, d107765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d10981, d107765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d10982 q = 0) : d107766 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10982, d107766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10982, d107766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11003 q = 0) : d107787 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11003, d107787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11003, d107787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11004 q = 0) : d107788 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11004, d107788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11004, d107788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d11005 q = 0) : d107789 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11005, d107789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11005, d107789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro7490 (p : Pattern) (selected : d11007 p = 0) : d107791 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10993 q = 0) : d107777 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10993, d107777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7464 q selected
    | true =>
      simp only [d10993, d107777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10994 q = 0) : d107778 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10994, d107778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10994, d107778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10995 q = 0) : d107779 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10995, d107779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d10995, d107779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d10996 q = 0) : d107780 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10996, d107780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10996, d107780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d10997 q = 0) : d107781 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10997, d107781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10997, d107781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11007 q = 0) : d107791 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11007, d107791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11007, d107791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro7491 (p : Pattern) (selected : d11018 p = 0) : d107802 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11013 q = 0) : d107797 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11013, d107797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro301 q selected
    | true =>
      simp only [d11013, d107797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11014 q = 0) : d107798 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11014, d107798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11014, d107798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11015 q = 0) : d107799 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11015, d107799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11015, d107799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10814 q = 0) : d107636 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10814, d107636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro253 q selected
    | true =>
      simp only [d10814, d107636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10815 q = 0) : d107637 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10815, d107637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10815, d107637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10816 q = 0) : d107638 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10816, d107638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10816, d107638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11016 q = 0) : d107800 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11016, d107800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11016, d107800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d10686 q = 0) : d107523 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, d107523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro222 q selected
    | true =>
      simp only [d10686, d107523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d10687 q = 0) : d107524 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d107524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10687, d107524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d10688 q = 0) : d107525 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d107525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10688, d107525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d10817 q = 0) : d107639 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10817, d107639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d10817, d107639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d11017 q = 0) : d107801 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11017, d107801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11017, d107801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d11018 q = 0) : d107802 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11018, d107802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d11018, d107802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro7492 (p : Pattern) (selected : d11023 p = 0) : d107807 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10814 q = 0) : d107636 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10814, d107636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro253 q selected
    | true =>
      simp only [d10814, d107636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10815 q = 0) : d107637 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10815, d107637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10815, d107637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10816 q = 0) : d107638 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10816, d107638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10816, d107638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10686 q = 0) : d107523 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, d107523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro222 q selected
    | true =>
      simp only [d10686, d107523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10687 q = 0) : d107524 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d107524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10687, d107524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10688 q = 0) : d107525 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d107525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10688, d107525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d10817 q = 0) : d107639 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10817, d107639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d10817, d107639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11021 q = 0) : d107805 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11021, d107805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11021, d107805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11022 q = 0) : d107806 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11022, d107806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11022, d107806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11023 q = 0) : d107807 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11023, d107807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d11023, d107807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro7493 (p : Pattern) (selected : d11029 p = 0) : d107813 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11019 q = 0) : d107803 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11019, d107803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7491 q selected
    | true =>
      simp only [d11019, d107803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11020 q = 0) : d107804 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11020, d107804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11020, d107804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11024 q = 0) : d107808 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11024, d107808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7492 q selected
    | true =>
      simp only [d11024, d107808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11025 q = 0) : d107809 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11025, d107809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11025, d107809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11026 q = 0) : d107810 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11026, d107810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11026, d107810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11027 q = 0) : d107811 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11027, d107811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11027, d107811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11028 q = 0) : d107812 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11028, d107812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11028, d107812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11029 q = 0) : d107813 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11029, d107813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11029, d107813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7494 (p : Pattern) (selected : d11031 p = 0) : d107815 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10686 q = 0) : d107523 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, d107523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro222 q selected
    | true =>
      simp only [d10686, d107523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10687 q = 0) : d107524 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d107524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10687, d107524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10688 q = 0) : d107525 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d107525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10688, d107525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11021 q = 0) : d107805 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11021, d107805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11021, d107805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11030 q = 0) : d107814 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11030, d107814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11030, d107814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11031 q = 0) : d107815 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11031, d107815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11031, d107815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7495 (p : Pattern) (selected : d11037 p = 0) : d107821 p = 1 := by
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
  have h3 (q : Pattern) (selected : d11032 q = 0) : d107816 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11032, d107816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7494 q selected
    | true =>
      simp only [d11032, d107816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11033 q = 0) : d107817 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11033, d107817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11033, d107817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11034 q = 0) : d107818 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11034, d107818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11034, d107818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11035 q = 0) : d107819 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11035, d107819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11035, d107819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11036 q = 0) : d107820 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11036, d107820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11036, d107820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11037 q = 0) : d107821 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11037, d107821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11037, d107821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7496 (p : Pattern) (selected : d11045 p = 0) : d107807 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11039 q = 0) : d107636 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11039, d107636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro307 q selected
    | true =>
      simp only [d11039, d107636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11040 q = 0) : d107637 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11040, d107637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11040, d107637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11041 q = 0) : d107638 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11041, d107638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11041, d107638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d10827 q = 0) : d107523 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10827, d107523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro256 q selected
    | true =>
      simp only [d10827, d107523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d10828 q = 0) : d107524 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10828, d107524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10828, d107524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d10829 q = 0) : d107525 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10829, d107525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10829, d107525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d11042 q = 0) : d107639 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11042, d107639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11042, d107639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d11043 q = 0) : d107805 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11043, d107805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11043, d107805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d11044 q = 0) : d107806 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11044, d107806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11044, d107806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d11045 q = 0) : d107807 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11045, d107807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d11045, d107807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro7497 (p : Pattern) (selected : d11049 p = 0) : d107815 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d10827 q = 0) : d107523 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10827, d107523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro256 q selected
    | true =>
      simp only [d10827, d107523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d10828 q = 0) : d107524 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10828, d107524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10828, d107524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d10829 q = 0) : d107525 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10829, d107525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10829, d107525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d11043 q = 0) : d107805 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11043, d107805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11043, d107805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11048 q = 0) : d107814 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11048, d107814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11048, d107814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11049 q = 0) : d107815 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11049, d107815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11049, d107815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro7498 (p : Pattern) (selected : d11055 p = 0) : d107821 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11046 q = 0) : d107808 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11046, d107808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7496 q selected
    | true =>
      simp only [d11046, d107808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11047 q = 0) : d107809 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11047, d107809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11047, d107809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11050 q = 0) : d107816 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11050, d107816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7497 q selected
    | true =>
      simp only [d11050, d107816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11051 q = 0) : d107817 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11051, d107817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11051, d107817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d11052 q = 0) : d107818 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11052, d107818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11052, d107818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d11053 q = 0) : d107819 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11053, d107819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11053, d107819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d11054 q = 0) : d107820 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11054, d107820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d11054, d107820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d11055 q = 0) : d107821 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11055, d107821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d11055, d107821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro7499 (p : Pattern) (selected : d11059 p = 0) : d107826 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d11050 q = 0) : d107816 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11050, d107816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7497 q selected
    | true =>
      simp only [d11050, d107816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d11051 q = 0) : d107817 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11051, d107817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d11051, d107817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d11056 q = 0) : d107823 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11056, d107823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d11056, d107823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d11057 q = 0) : d107824 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11057, d107824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d11057, d107824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d11058 q = 0) : d107825 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11058, d107825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d11058, d107825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d11059 q = 0) : d107826 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11059, d107826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d11059, d107826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
end NetHack.Soko22Hazard87
