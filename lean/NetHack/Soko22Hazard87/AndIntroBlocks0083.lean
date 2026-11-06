import NetHack.Soko22Hazard87.AndIntroBlocks0082
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro20750 (p : Pattern) (ha : d84050 p = 1) (hb : d112009 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d977 q = 1) (hb : d52596 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d977, d52596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro127 q ha hb
    | true =>
      simp only [d977, d52596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro128 q ha hb
  have h2 (q : Pattern) (ha : d978 q = 1) (hb : d52597 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d978, d52597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d978, d52597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d979 q = 1) (hb : d52598 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d979, d52598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d979, d52598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52603 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8689 q = 1) (hb : d52604 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8689, d52604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8689, d52604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84049 q = 1) (hb : d112008 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84049, d112008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d84049, d112008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84050 q = 1) (hb : d112009 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84050, d112009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84050, d112009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro20751 (p : Pattern) (ha : d84060 p = 1) (hb : d112015 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84051 q = 1) (hb : d112010 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84051, d112010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20750 q ha hb
    | true =>
      simp only [d84051, d112010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84052 q = 1) (hb : d112011 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84052, d112011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84052, d112011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84055 q = 1) (hb : d98939 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84055, d98939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14192 q ha hb
    | true =>
      simp only [d84055, d98939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84056 q = 1) (hb : d98940 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84056, d98940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84056, d98940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84057 q = 1) (hb : d112012 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84057, d112012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84057, d112012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84058 q = 1) (hb : d112013 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84058, d112013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84058, d112013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84059 q = 1) (hb : d112014 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84059, d112014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84059, d112014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84060 q = 1) (hb : d112015 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84060, d112015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84060, d112015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20752 (p : Pattern) (ha : d84064 p = 1) (hb : d112019 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84055 q = 1) (hb : d98939 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84055, d98939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14192 q ha hb
    | true =>
      simp only [d84055, d98939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84056 q = 1) (hb : d98940 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84056, d98940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84056, d98940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1006 q = 1) (hb : d52625 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d52625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro117 q ha hb
    | true =>
      simp only [d1006, d52625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1007 q = 1) (hb : d52626 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d52626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d52626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84061 q = 1) (hb : d112016 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84061, d112016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84061, d112016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84062 q = 1) (hb : d112017 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84062, d112017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84062, d112017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84063 q = 1) (hb : d112018 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84063, d112018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84063, d112018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84064 q = 1) (hb : d112019 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84064, d112019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84064, d112019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20753 (p : Pattern) (ha : d84071 p = 1) (hb : d112025 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84055 q = 1) (hb : d98939 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84055, d98939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14192 q ha hb
    | true =>
      simp only [d84055, d98939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84056 q = 1) (hb : d98940 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84056, d98940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84056, d98940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84068 q = 1) (hb : d112022 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84068, d112022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84068, d112022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84069 q = 1) (hb : d112023 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84069, d112023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84069, d112023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84070 q = 1) (hb : d112024 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84070, d112024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84070, d112024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84071 q = 1) (hb : d112025 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84071, d112025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84071, d112025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20754 (p : Pattern) (ha : d84077 p = 1) (hb : d112031 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84065 q = 1) (hb : d112020 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84065, d112020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20751 q ha hb
    | true =>
      simp only [d84065, d112020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20752 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84066 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84067 q = 1) (hb : d112021 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84067, d112021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84067, d112021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d84072 q = 1) (hb : d112026 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84072, d112026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20753 q ha hb
    | true =>
      simp only [d84072, d112026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84073 q = 1) (hb : d112027 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84073, d112027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84073, d112027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84074 q = 1) (hb : d112028 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84074, d112028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84074, d112028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84075 q = 1) (hb : d112029 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84075, d112029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84075, d112029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84076 q = 1) (hb : d112030 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84076, d112030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84076, d112030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84077 q = 1) (hb : d112031 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84077, d112031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84077, d112031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro20755 (p : Pattern) (ha : d84083 p = 1) (hb : d112037 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83972 q = 1) (hb : d111931 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83972, d111931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83972, d111931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20734 q ha hb
  have h2 (q : Pattern) (ha : d83973 q = 1) (hb : d111932 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83973, d111932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83973, d111932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d83981 q = 1) (hb : d111940 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83981, d111940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20734 q ha hb
    | true =>
      simp only [d83981, d111940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20736 q ha hb
  have h4 (q : Pattern) (ha : d83982 q = 1) (hb : d111941 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83982, d111941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83982, d111941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83983 q = 1) (hb : d111942 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83983, d111942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d83983, d111942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84035 q = 1) (hb : d111994 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84035, d111994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20742 q ha hb
    | true =>
      simp only [d84035, d111994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20747 q ha hb
  have h7 (q : Pattern) (ha : d84037 q = 1) (hb : d111996 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84037, d111996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20748 q ha hb
    | true =>
      simp only [d84037, d111996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro113 q hb ha
  have h8 (q : Pattern) (ha : d84038 q = 1) (hb : d111997 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84038, d111997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84038, d111997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84039 q = 1) (hb : d111998 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84039, d111998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84039, d111998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d84040 q = 1) (hb : d111999 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84040, d111999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84040, d111999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84044 q = 1) (hb : d112003 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84044, d112003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84044, d112003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20749 q ha hb
  have h12 (q : Pattern) (ha : d960 q = 1) (hb : d52579 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, d52579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d960, d52579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro114 q ha hb
  have h13 (q : Pattern) (ha : d84045 q = 1) (hb : d112004 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84045, d112004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d84045, d112004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d84046 q = 1) (hb : d112005 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84046, d112005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84046, d112005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d84047 q = 1) (hb : d112006 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84047, d112006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d84047, d112006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d84048 q = 1) (hb : d112007 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84048, d112007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84048, d112007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d84078 q = 1) (hb : d112032 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84078, d112032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84078, d112032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20754 q ha hb
  have h18 (q : Pattern) (ha : d1070 q = 1) (hb : d52651 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1070, d52651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1070, d52651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro119 q ha hb
  have h19 (q : Pattern) (ha : d84079 q = 1) (hb : d112033 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84079, d112033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84079, d112033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d84080 q = 1) (hb : d112034 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84080, d112034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d84080, d112034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d84081 q = 1) (hb : d112035 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84081, d112035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d84081, d112035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d84082 q = 1) (hb : d112036 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84082, d112036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d84082, d112036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d84083 q = 1) (hb : d112037 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d84083, d112037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d84083, d112037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro20756 (p : Pattern) (ha : d84089 p = 1) (hb : d112043 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84084 q = 1) (hb : d112038 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d84084, d112038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84084, d112038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20755 q ha hb
  have h2 (q : Pattern) (ha : d84085 q = 1) (hb : d112039 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d84085, d112039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84085, d112039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84086 q = 1) (hb : d112040 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d84086, d112040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84086, d112040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d84087 q = 1) (hb : d112041 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d84087, d112041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84087, d112041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84088 q = 1) (hb : d112042 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d84088, d112042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84088, d112042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84089 q = 1) (hb : d112043 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d84089, d112043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84089, d112043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20757 (p : Pattern) (ha : d84099 p = 1) (hb : d112049 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84094 q = 1) (hb : d98967 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84094, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14204 q ha hb
    | true =>
      simp only [d84094, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84095 q = 1) (hb : d98968 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84095, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84095, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84096 q = 1) (hb : d112046 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84096, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84096, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84097 q = 1) (hb : d112047 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84097, d112047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84097, d112047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84098 q = 1) (hb : d112048 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84098, d112048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84098, d112048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84099 q = 1) (hb : d112049 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84099, d112049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84099, d112049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20758 (p : Pattern) (ha : d84105 p = 1) (hb : d112055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84100 q = 1) (hb : d112050 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84100, d112050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20757 q ha hb
    | true =>
      simp only [d84100, d112050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q hb ha
  have h2 (q : Pattern) (ha : d84101 q = 1) (hb : d112051 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84101, d112051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84101, d112051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84102 q = 1) (hb : d112052 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84102, d112052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84102, d112052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84103 q = 1) (hb : d112053 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84103, d112053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84103, d112053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84104 q = 1) (hb : d112054 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84104, d112054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84104, d112054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84105 q = 1) (hb : d112055 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84105, d112055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84105, d112055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20759 (p : Pattern) (ha : d84108 p = 1) (hb : d112058 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84094 q = 1) (hb : d98967 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84094, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14204 q ha hb
    | true =>
      simp only [d84094, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84095 q = 1) (hb : d98968 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84095, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84095, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84096 q = 1) (hb : d112046 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84096, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84096, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84097 q = 1) (hb : d112047 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84097, d112047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84097, d112047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84098 q = 1) (hb : d112048 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84098, d112048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84098, d112048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84108 q = 1) (hb : d112058 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84108, d112058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84108, d112058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20760 (p : Pattern) (ha : d84114 p = 1) (hb : d112064 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84100 q = 1) (hb : d112050 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84100, d112050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20757 q ha hb
    | true =>
      simp only [d84100, d112050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q hb ha
  have h2 (q : Pattern) (ha : d84101 q = 1) (hb : d112051 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84101, d112051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84101, d112051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84102 q = 1) (hb : d112052 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84102, d112052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84102, d112052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84103 q = 1) (hb : d112053 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84103, d112053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84103, d112053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84104 q = 1) (hb : d112054 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84104, d112054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84104, d112054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84109 q = 1) (hb : d112059 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84109, d112059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20759 q ha hb
    | true =>
      simp only [d84109, d112059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro162 q hb ha
  have h7 (q : Pattern) (ha : d84110 q = 1) (hb : d112060 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84110, d112060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84110, d112060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84111 q = 1) (hb : d112061 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84111, d112061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84111, d112061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d84112 q = 1) (hb : d112062 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84112, d112062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84112, d112062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84113 q = 1) (hb : d112063 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84113, d112063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84113, d112063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84114 q = 1) (hb : d112064 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84114, d112064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84114, d112064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro20761 (p : Pattern) (ha : d84119 p = 1) (hb : d112069 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84094 q = 1) (hb : d98967 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84094, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14204 q ha hb
    | true =>
      simp only [d84094, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84095 q = 1) (hb : d98968 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84095, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84095, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84096 q = 1) (hb : d112046 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84096, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84096, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84097 q = 1) (hb : d112047 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84097, d112047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84097, d112047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84118 q = 1) (hb : d112068 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84118, d112068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84118, d112068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84119 q = 1) (hb : d112069 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84119, d112069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84119, d112069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20762 (p : Pattern) (ha : d84126 p = 1) (hb : d112076 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84094 q = 1) (hb : d98967 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84094, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14204 q ha hb
    | true =>
      simp only [d84094, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84095 q = 1) (hb : d98968 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84095, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84095, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84096 q = 1) (hb : d112046 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84096, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84096, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84124 q = 1) (hb : d112074 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84124, d112074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84124, d112074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84125 q = 1) (hb : d112075 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84125, d112075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84125, d112075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84126 q = 1) (hb : d112076 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84126, d112076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84126, d112076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20763 (p : Pattern) (ha : d84131 p = 1) (hb : d112081 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1216 q = 1) (hb : d52797 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1216, d52797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro175 q ha hb
    | true =>
      simp only [d1216, d52797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro152 q ha hb
  have h2 (q : Pattern) (ha : d1217 q = 1) (hb : d52798 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1217, d52798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1217, d52798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1218 q = 1) (hb : d52799 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1218, d52799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1218, d52799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52712 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8780 q = 1) (hb : d52800 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8780, d52800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8780, d52800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84130 q = 1) (hb : d112080 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84130, d112080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d84130, d112080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84131 q = 1) (hb : d112081 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84131, d112081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84131, d112081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro20764 (p : Pattern) (ha : d84137 p = 1) (hb : d112087 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84132 q = 1) (hb : d112082 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84132, d112082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20763 q ha hb
    | true =>
      simp only [d84132, d112082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84133 q = 1) (hb : d112083 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84133, d112083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84133, d112083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84094 q = 1) (hb : d98967 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84094, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14204 q ha hb
    | true =>
      simp only [d84094, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84095 q = 1) (hb : d98968 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84095, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84095, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84134 q = 1) (hb : d112084 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84134, d112084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84134, d112084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84135 q = 1) (hb : d112085 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84135, d112085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84135, d112085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84136 q = 1) (hb : d112086 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84136, d112086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84136, d112086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84137 q = 1) (hb : d112087 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84137, d112087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84137, d112087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20765 (p : Pattern) (ha : d84143 p = 1) (hb : d112093 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84094 q = 1) (hb : d98967 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84094, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14204 q ha hb
    | true =>
      simp only [d84094, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84095 q = 1) (hb : d98968 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84095, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84095, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84140 q = 1) (hb : d112090 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84140, d112090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84140, d112090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84141 q = 1) (hb : d112091 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84141, d112091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84141, d112091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84142 q = 1) (hb : d112092 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84142, d112092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84142, d112092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84143 q = 1) (hb : d112093 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84143, d112093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84143, d112093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20766 (p : Pattern) (ha : d84149 p = 1) (hb : d112099 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84120 q = 1) (hb : d112070 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84120, d112070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20761 q ha hb
    | true =>
      simp only [d84120, d112070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro187 q hb ha
  have h2 (q : Pattern) (ha : d84121 q = 1) (hb : d112071 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84121, d112071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84121, d112071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84122 q = 1) (hb : d112072 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84122, d112072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84122, d112072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84123 q = 1) (hb : d112073 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84123, d112073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84123, d112073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84127 q = 1) (hb : d112077 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84127, d112077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20762 q ha hb
    | true =>
      simp only [d84127, d112077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro189 q hb ha
  have h6 (q : Pattern) (ha : d84128 q = 1) (hb : d112078 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84128, d112078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84128, d112078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84129 q = 1) (hb : d112079 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84129, d112079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84129, d112079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84138 q = 1) (hb : d112088 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84138, d112088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20764 q ha hb
    | true =>
      simp only [d84138, d112088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20757 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d84100 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d84139 q = 1) (hb : d112089 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84139, d112089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84139, d112089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d84144 q = 1) (hb : d112094 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84144, d112094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20765 q ha hb
    | true =>
      simp only [d84144, d112094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d84145 q = 1) (hb : d112095 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84145, d112095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d84145, d112095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d84146 q = 1) (hb : d112096 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84146, d112096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84146, d112096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d84147 q = 1) (hb : d112097 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84147, d112097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84147, d112097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d84148 q = 1) (hb : d112098 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84148, d112098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84148, d112098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d84149 q = 1) (hb : d112099 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84149, d112099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84149, d112099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro20767 (p : Pattern) (ha : d84150 p = 1) (hb : d112100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84094 q = 1) (hb : d98967 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84094, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14204 q ha hb
    | true =>
      simp only [d84094, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84095 q = 1) (hb : d98968 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84095, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84095, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84096 q = 1) (hb : d112046 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84096, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84096, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84097 q = 1) (hb : d112047 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84097, d112047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84097, d112047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84118 q = 1) (hb : d112068 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84118, d112068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84118, d112068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84150 q = 1) (hb : d112100 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84150, d112100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84150, d112100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20768 (p : Pattern) (ha : d84155 p = 1) (hb : d112105 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84094 q = 1) (hb : d98967 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84094, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14204 q ha hb
    | true =>
      simp only [d84094, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84095 q = 1) (hb : d98968 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84095, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84095, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84096 q = 1) (hb : d112046 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84096, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84096, d112046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84124 q = 1) (hb : d112074 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84124, d112074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84124, d112074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84125 q = 1) (hb : d112075 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84125, d112075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84125, d112075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84155 q = 1) (hb : d112105 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84155, d112105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84155, d112105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20769 (p : Pattern) (ha : d84159 p = 1) (hb : d112109 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84132 q = 1) (hb : d112082 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84132, d112082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20763 q ha hb
    | true =>
      simp only [d84132, d112082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84133 q = 1) (hb : d112083 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84133, d112083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84133, d112083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84094 q = 1) (hb : d98967 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84094, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14204 q ha hb
    | true =>
      simp only [d84094, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84095 q = 1) (hb : d98968 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84095, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84095, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84134 q = 1) (hb : d112084 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84134, d112084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84134, d112084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84135 q = 1) (hb : d112085 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84135, d112085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84135, d112085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84136 q = 1) (hb : d112086 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84136, d112086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84136, d112086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84159 q = 1) (hb : d112109 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84159, d112109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84159, d112109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20770 (p : Pattern) (ha : d84162 p = 1) (hb : d112112 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84094 q = 1) (hb : d98967 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84094, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14204 q ha hb
    | true =>
      simp only [d84094, d98967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84095 q = 1) (hb : d98968 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84095, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84095, d98968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84140 q = 1) (hb : d112090 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84140, d112090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84140, d112090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84141 q = 1) (hb : d112091 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84141, d112091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84141, d112091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84142 q = 1) (hb : d112092 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84142, d112092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84142, d112092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84162 q = 1) (hb : d112112 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84162, d112112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84162, d112112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20771 (p : Pattern) (ha : d84168 p = 1) (hb : d112118 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84120 q = 1) (hb : d112070 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84120, d112070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20761 q ha hb
    | true =>
      simp only [d84120, d112070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro187 q hb ha
  have h2 (q : Pattern) (ha : d84121 q = 1) (hb : d112071 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84121, d112071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84121, d112071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84122 q = 1) (hb : d112072 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84122, d112072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84122, d112072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84123 q = 1) (hb : d112073 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84123, d112073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84123, d112073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84127 q = 1) (hb : d112077 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84127, d112077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20762 q ha hb
    | true =>
      simp only [d84127, d112077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro189 q hb ha
  have h6 (q : Pattern) (ha : d84128 q = 1) (hb : d112078 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84128, d112078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84128, d112078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84129 q = 1) (hb : d112079 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84129, d112079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84129, d112079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84138 q = 1) (hb : d112088 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84138, d112088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20764 q ha hb
    | true =>
      simp only [d84138, d112088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20757 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d84100 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d84139 q = 1) (hb : d112089 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84139, d112089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84139, d112089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d84144 q = 1) (hb : d112094 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84144, d112094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20765 q ha hb
    | true =>
      simp only [d84144, d112094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d84145 q = 1) (hb : d112095 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84145, d112095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d84145, d112095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d84146 q = 1) (hb : d112096 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84146, d112096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84146, d112096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d84147 q = 1) (hb : d112097 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84147, d112097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84147, d112097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d84148 q = 1) (hb : d112098 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84148, d112098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84148, d112098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d84151 q = 1) (hb : d112101 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84151, d112101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20767 q ha hb
    | true =>
      simp only [d84151, d112101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro193 q hb ha
  have h17 (q : Pattern) (ha : d84152 q = 1) (hb : d112102 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84152, d112102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84152, d112102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d84153 q = 1) (hb : d112103 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84153, d112103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84153, d112103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d84154 q = 1) (hb : d112104 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84154, d112104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84154, d112104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d84156 q = 1) (hb : d112106 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84156, d112106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20768 q ha hb
    | true =>
      simp only [d84156, d112106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro195 q hb ha
  have h21 (q : Pattern) (ha : d84157 q = 1) (hb : d112107 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84157, d112107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84157, d112107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d84158 q = 1) (hb : d112108 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84158, d112108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d84158, d112108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d84160 q = 1) (hb : d112110 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84160, d112110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20769 q ha hb
    | true =>
      simp only [d84160, d112110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20759 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d84109 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d84161 q = 1) (hb : d112111 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84161, d112111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d84161, d112111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d84163 q = 1) (hb : d112113 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84163, d112113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20770 q ha hb
    | true =>
      simp only [d84163, d112113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d84164 q = 1) (hb : d112114 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84164, d112114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d84164, d112114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d84165 q = 1) (hb : d112115 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84165, d112115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d84165, d112115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d84166 q = 1) (hb : d112116 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84166, d112116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d84166, d112116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d84167 q = 1) (hb : d112117 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84167, d112117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d84167, d112117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d84168 q = 1) (hb : d112118 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84168, d112118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d84168, d112118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro20772 (p : Pattern) (ha : d84170 p = 1) (hb : d112120 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84100 q = 1) (hb : d112050 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84100, d112050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20757 q ha hb
    | true =>
      simp only [d84100, d112050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q hb ha
  have h2 (q : Pattern) (ha : d84101 q = 1) (hb : d112051 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84101, d112051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84101, d112051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84102 q = 1) (hb : d112052 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84102, d112052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84102, d112052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84103 q = 1) (hb : d112053 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84103, d112053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84103, d112053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84104 q = 1) (hb : d112054 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84104, d112054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84104, d112054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1350 q = 1) (hb : d52838 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, d52838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q ha hb
    | true =>
      simp only [d1350, d52838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1351 q = 1) (hb : d52839 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, d52839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1351, d52839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1352 q = 1) (hb : d52840 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, d52840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1352, d52840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1353 q = 1) (hb : d52841 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, d52841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, d52841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1354 q = 1) (hb : d52842 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, d52842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, d52842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84170 q = 1) (hb : d112120 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84170, d112120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84170, d112120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro20773 (p : Pattern) (ha : d84177 p = 1) (hb : d112127 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84160 q = 1) (hb : d112110 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84160, d112110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20769 q ha hb
    | true =>
      simp only [d84160, d112110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20759 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84109 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84161 q = 1) (hb : d112111 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84161, d112111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84161, d112111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d84163 q = 1) (hb : d112113 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84163, d112113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20770 q ha hb
    | true =>
      simp only [d84163, d112113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84164 q = 1) (hb : d112114 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84164, d112114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84164, d112114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84165 q = 1) (hb : d112115 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84165, d112115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84165, d112115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84175 q = 1) (hb : d112125 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84175, d112125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84175, d112125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84176 q = 1) (hb : d112126 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84176, d112126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84176, d112126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84177 q = 1) (hb : d112127 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84177, d112127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84177, d112127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro20774 (p : Pattern) (ha : d84184 p = 1) (hb : d112134 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1397 q = 1) (hb : d52885 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1397, d52885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro179 q ha hb
    | true =>
      simp only [d1397, d52885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro180 q ha hb
  have h2 (q : Pattern) (ha : d1398 q = 1) (hb : d52886 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1398, d52886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1398, d52886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1399 q = 1) (hb : d52887 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1399, d52887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1399, d52887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52892 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8856 q = 1) (hb : d52893 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8856, d52893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8856, d52893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84183 q = 1) (hb : d112133 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84183, d112133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d84183, d112133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84184 q = 1) (hb : d112134 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84184, d112134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84184, d112134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro20775 (p : Pattern) (ha : d84194 p = 1) (hb : d112140 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84185 q = 1) (hb : d112135 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84185, d112135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20774 q ha hb
    | true =>
      simp only [d84185, d112135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84186 q = 1) (hb : d112136 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84186, d112136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84186, d112136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84189 q = 1) (hb : d99000 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84189, d99000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14213 q ha hb
    | true =>
      simp only [d84189, d99000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84190 q = 1) (hb : d99001 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84190, d99001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84190, d99001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84191 q = 1) (hb : d112137 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84191, d112137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84191, d112137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84192 q = 1) (hb : d112138 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84192, d112138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84192, d112138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84193 q = 1) (hb : d112139 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84193, d112139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84193, d112139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84194 q = 1) (hb : d112140 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84194, d112140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84194, d112140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20776 (p : Pattern) (ha : d84198 p = 1) (hb : d112144 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84189 q = 1) (hb : d99000 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84189, d99000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14213 q ha hb
    | true =>
      simp only [d84189, d99000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84190 q = 1) (hb : d99001 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84190, d99001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84190, d99001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1431 q = 1) (hb : d52919 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1431, d52919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro169 q ha hb
    | true =>
      simp only [d1431, d52919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1432 q = 1) (hb : d52920 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1432, d52920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1432, d52920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84195 q = 1) (hb : d112141 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84195, d112141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84195, d112141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84196 q = 1) (hb : d112142 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84196, d112142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84196, d112142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84197 q = 1) (hb : d112143 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84197, d112143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84197, d112143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84198 q = 1) (hb : d112144 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84198, d112144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84198, d112144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20777 (p : Pattern) (ha : d84205 p = 1) (hb : d112150 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84189 q = 1) (hb : d99000 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84189, d99000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14213 q ha hb
    | true =>
      simp only [d84189, d99000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84190 q = 1) (hb : d99001 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84190, d99001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84190, d99001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84202 q = 1) (hb : d112147 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84202, d112147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84202, d112147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84203 q = 1) (hb : d112148 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84203, d112148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84203, d112148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84204 q = 1) (hb : d112149 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84204, d112149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84204, d112149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84205 q = 1) (hb : d112150 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84205, d112150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84205, d112150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20778 (p : Pattern) (ha : d84211 p = 1) (hb : d112156 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84199 q = 1) (hb : d112145 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84199, d112145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20775 q ha hb
    | true =>
      simp only [d84199, d112145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20776 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84200 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84201 q = 1) (hb : d112146 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84201, d112146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84201, d112146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d84206 q = 1) (hb : d112151 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84206, d112151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20777 q ha hb
    | true =>
      simp only [d84206, d112151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84207 q = 1) (hb : d112152 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84207, d112152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84207, d112152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84208 q = 1) (hb : d112153 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84208, d112153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84208, d112153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84209 q = 1) (hb : d112154 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84209, d112154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84209, d112154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84210 q = 1) (hb : d112155 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84210, d112155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84210, d112155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84211 q = 1) (hb : d112156 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84211, d112156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84211, d112156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro20779 (p : Pattern) (ha : d84217 p = 1) (hb : d112162 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84106 q = 1) (hb : d112056 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84106, d112056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84106, d112056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20758 q ha hb
  have h2 (q : Pattern) (ha : d84107 q = 1) (hb : d112057 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84107, d112057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84107, d112057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84115 q = 1) (hb : d112065 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84115, d112065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20758 q ha hb
    | true =>
      simp only [d84115, d112065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20760 q ha hb
  have h4 (q : Pattern) (ha : d84116 q = 1) (hb : d112066 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84116, d112066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84116, d112066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84117 q = 1) (hb : d112067 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84117, d112067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84117, d112067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84169 q = 1) (hb : d112119 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84169, d112119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20766 q ha hb
    | true =>
      simp only [d84169, d112119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20771 q ha hb
  have h7 (q : Pattern) (ha : d84171 q = 1) (hb : d112121 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84171, d112121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20772 q ha hb
    | true =>
      simp only [d84171, d112121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro165 q hb ha
  have h8 (q : Pattern) (ha : d84172 q = 1) (hb : d112122 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84172, d112122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84172, d112122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84173 q = 1) (hb : d112123 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84173, d112123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84173, d112123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d84174 q = 1) (hb : d112124 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84174, d112124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84174, d112124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84178 q = 1) (hb : d112128 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84178, d112128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84178, d112128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20773 q ha hb
  have h12 (q : Pattern) (ha : d1371 q = 1) (hb : d52859 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1371, d52859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1371, d52859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro166 q ha hb
  have h13 (q : Pattern) (ha : d84179 q = 1) (hb : d112129 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84179, d112129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d84179, d112129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d84180 q = 1) (hb : d112130 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84180, d112130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84180, d112130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d84181 q = 1) (hb : d112131 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84181, d112131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d84181, d112131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d84182 q = 1) (hb : d112132 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84182, d112132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84182, d112132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d84212 q = 1) (hb : d112157 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84212, d112157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84212, d112157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20778 q ha hb
  have h18 (q : Pattern) (ha : d1504 q = 1) (hb : d52945 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1504, d52945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1504, d52945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro171 q ha hb
  have h19 (q : Pattern) (ha : d84213 q = 1) (hb : d112158 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84213, d112158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84213, d112158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d84214 q = 1) (hb : d112159 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84214, d112159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d84214, d112159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d84215 q = 1) (hb : d112160 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84215, d112160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d84215, d112160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d84216 q = 1) (hb : d112161 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84216, d112161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d84216, d112161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d84217 q = 1) (hb : d112162 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d84217, d112162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d84217, d112162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro20780 (p : Pattern) (ha : d84223 p = 1) (hb : d112168 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84218 q = 1) (hb : d112163 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d84218, d112163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84218, d112163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20779 q ha hb
  have h2 (q : Pattern) (ha : d84219 q = 1) (hb : d112164 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d84219, d112164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84219, d112164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84220 q = 1) (hb : d112165 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d84220, d112165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84220, d112165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d84221 q = 1) (hb : d112166 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d84221, d112166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84221, d112166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84222 q = 1) (hb : d112167 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d84222, d112167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84222, d112167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84223 q = 1) (hb : d112168 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d84223, d112168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84223, d112168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20781 (p : Pattern) (ha : d84234 p = 1) (hb : d112175 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84229 q = 1) (hb : d99029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84229, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14225 q ha hb
    | true =>
      simp only [d84229, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84230 q = 1) (hb : d99030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84230, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84230, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84231 q = 1) (hb : d112172 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84231, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84231, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84232 q = 1) (hb : d112173 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84232, d112173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84232, d112173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84233 q = 1) (hb : d112174 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84233, d112174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84233, d112174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84234 q = 1) (hb : d112175 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84234, d112175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84234, d112175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20782 (p : Pattern) (ha : d84240 p = 1) (hb : d112181 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84235 q = 1) (hb : d112176 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84235, d112176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20781 q ha hb
    | true =>
      simp only [d84235, d112176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q hb ha
  have h2 (q : Pattern) (ha : d84236 q = 1) (hb : d112177 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84236, d112177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84236, d112177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84237 q = 1) (hb : d112178 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84237, d112178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84237, d112178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84238 q = 1) (hb : d112179 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84238, d112179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84238, d112179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84239 q = 1) (hb : d112180 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84239, d112180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84239, d112180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84240 q = 1) (hb : d112181 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84240, d112181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84240, d112181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20783 (p : Pattern) (ha : d84243 p = 1) (hb : d112184 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84229 q = 1) (hb : d99029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84229, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14225 q ha hb
    | true =>
      simp only [d84229, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84230 q = 1) (hb : d99030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84230, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84230, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84231 q = 1) (hb : d112172 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84231, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84231, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84232 q = 1) (hb : d112173 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84232, d112173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84232, d112173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84233 q = 1) (hb : d112174 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84233, d112174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84233, d112174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84243 q = 1) (hb : d112184 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84243, d112184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84243, d112184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20784 (p : Pattern) (ha : d84249 p = 1) (hb : d112190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84235 q = 1) (hb : d112176 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84235, d112176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20781 q ha hb
    | true =>
      simp only [d84235, d112176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q hb ha
  have h2 (q : Pattern) (ha : d84236 q = 1) (hb : d112177 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84236, d112177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84236, d112177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84237 q = 1) (hb : d112178 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84237, d112178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84237, d112178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84238 q = 1) (hb : d112179 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84238, d112179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84238, d112179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84239 q = 1) (hb : d112180 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84239, d112180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84239, d112180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84244 q = 1) (hb : d112185 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84244, d112185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20783 q ha hb
    | true =>
      simp only [d84244, d112185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro220 q hb ha
  have h7 (q : Pattern) (ha : d84245 q = 1) (hb : d112186 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84245, d112186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84245, d112186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84246 q = 1) (hb : d112187 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84246, d112187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84246, d112187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d84247 q = 1) (hb : d112188 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84247, d112188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84247, d112188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84248 q = 1) (hb : d112189 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84248, d112189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84248, d112189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84249 q = 1) (hb : d112190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84249, d112190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84249, d112190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro20785 (p : Pattern) (ha : d84254 p = 1) (hb : d112195 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84229 q = 1) (hb : d99029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84229, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14225 q ha hb
    | true =>
      simp only [d84229, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84230 q = 1) (hb : d99030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84230, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84230, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84231 q = 1) (hb : d112172 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84231, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84231, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84232 q = 1) (hb : d112173 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84232, d112173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84232, d112173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84253 q = 1) (hb : d112194 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84253, d112194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84253, d112194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84254 q = 1) (hb : d112195 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84254, d112195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84254, d112195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20786 (p : Pattern) (ha : d84261 p = 1) (hb : d112202 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84229 q = 1) (hb : d99029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84229, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14225 q ha hb
    | true =>
      simp only [d84229, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84230 q = 1) (hb : d99030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84230, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84230, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84231 q = 1) (hb : d112172 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84231, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84231, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84259 q = 1) (hb : d112200 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84259, d112200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84259, d112200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84260 q = 1) (hb : d112201 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84260, d112201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84260, d112201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84261 q = 1) (hb : d112202 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84261, d112202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84261, d112202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20787 (p : Pattern) (ha : d84266 p = 1) (hb : d112207 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1671 q = 1) (hb : d53112 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1671, d53112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro231 q ha hb
    | true =>
      simp only [d1671, d53112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro210 q ha hb
  have h2 (q : Pattern) (ha : d1672 q = 1) (hb : d53113 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1672, d53113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1672, d53113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1673 q = 1) (hb : d53114 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1673, d53114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1673, d53114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53033 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8948 q = 1) (hb : d53115 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d8948, d53115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8948, d53115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84265 q = 1) (hb : d112206 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84265, d112206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d84265, d112206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84266 q = 1) (hb : d112207 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84266, d112207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84266, d112207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro20788 (p : Pattern) (ha : d84272 p = 1) (hb : d112213 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84267 q = 1) (hb : d112208 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84267, d112208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20787 q ha hb
    | true =>
      simp only [d84267, d112208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84268 q = 1) (hb : d112209 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84268, d112209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84268, d112209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84229 q = 1) (hb : d99029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84229, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14225 q ha hb
    | true =>
      simp only [d84229, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84230 q = 1) (hb : d99030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84230, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84230, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84269 q = 1) (hb : d112210 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84269, d112210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84269, d112210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84270 q = 1) (hb : d112211 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84270, d112211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84270, d112211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84271 q = 1) (hb : d112212 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84271, d112212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84271, d112212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84272 q = 1) (hb : d112213 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84272, d112213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84272, d112213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20789 (p : Pattern) (ha : d84278 p = 1) (hb : d112219 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84229 q = 1) (hb : d99029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84229, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14225 q ha hb
    | true =>
      simp only [d84229, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84230 q = 1) (hb : d99030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84230, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84230, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84275 q = 1) (hb : d112216 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84275, d112216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84275, d112216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84276 q = 1) (hb : d112217 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84276, d112217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84276, d112217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84277 q = 1) (hb : d112218 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84277, d112218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84277, d112218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84278 q = 1) (hb : d112219 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84278, d112219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84278, d112219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20790 (p : Pattern) (ha : d84284 p = 1) (hb : d112225 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84255 q = 1) (hb : d112196 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84255, d112196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20785 q ha hb
    | true =>
      simp only [d84255, d112196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro243 q hb ha
  have h2 (q : Pattern) (ha : d84256 q = 1) (hb : d112197 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84256, d112197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84256, d112197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84257 q = 1) (hb : d112198 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84257, d112198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84257, d112198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84258 q = 1) (hb : d112199 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84258, d112199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84258, d112199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84262 q = 1) (hb : d112203 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84262, d112203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20786 q ha hb
    | true =>
      simp only [d84262, d112203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro245 q hb ha
  have h6 (q : Pattern) (ha : d84263 q = 1) (hb : d112204 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84263, d112204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84263, d112204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84264 q = 1) (hb : d112205 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84264, d112205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84264, d112205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84273 q = 1) (hb : d112214 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84273, d112214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20788 q ha hb
    | true =>
      simp only [d84273, d112214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20781 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d84235 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d84274 q = 1) (hb : d112215 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84274, d112215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84274, d112215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d84279 q = 1) (hb : d112220 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84279, d112220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20789 q ha hb
    | true =>
      simp only [d84279, d112220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d84280 q = 1) (hb : d112221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84280, d112221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d84280, d112221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d84281 q = 1) (hb : d112222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84281, d112222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84281, d112222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d84282 q = 1) (hb : d112223 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84282, d112223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84282, d112223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d84283 q = 1) (hb : d112224 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84283, d112224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84283, d112224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d84284 q = 1) (hb : d112225 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84284, d112225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84284, d112225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro20791 (p : Pattern) (ha : d84285 p = 1) (hb : d112226 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84229 q = 1) (hb : d99029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84229, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14225 q ha hb
    | true =>
      simp only [d84229, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84230 q = 1) (hb : d99030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84230, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84230, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84231 q = 1) (hb : d112172 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84231, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84231, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84232 q = 1) (hb : d112173 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84232, d112173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84232, d112173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84253 q = 1) (hb : d112194 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84253, d112194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84253, d112194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84285 q = 1) (hb : d112226 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84285, d112226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84285, d112226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20792 (p : Pattern) (ha : d84290 p = 1) (hb : d112231 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84229 q = 1) (hb : d99029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84229, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14225 q ha hb
    | true =>
      simp only [d84229, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84230 q = 1) (hb : d99030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84230, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84230, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84231 q = 1) (hb : d112172 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84231, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84231, d112172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84259 q = 1) (hb : d112200 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84259, d112200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84259, d112200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84260 q = 1) (hb : d112201 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84260, d112201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84260, d112201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84290 q = 1) (hb : d112231 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84290, d112231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84290, d112231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20793 (p : Pattern) (ha : d84294 p = 1) (hb : d112235 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84267 q = 1) (hb : d112208 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84267, d112208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20787 q ha hb
    | true =>
      simp only [d84267, d112208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84268 q = 1) (hb : d112209 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84268, d112209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84268, d112209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84229 q = 1) (hb : d99029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84229, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14225 q ha hb
    | true =>
      simp only [d84229, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84230 q = 1) (hb : d99030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84230, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84230, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84269 q = 1) (hb : d112210 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84269, d112210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84269, d112210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84270 q = 1) (hb : d112211 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84270, d112211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84270, d112211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84271 q = 1) (hb : d112212 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84271, d112212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84271, d112212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84294 q = 1) (hb : d112235 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84294, d112235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84294, d112235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20794 (p : Pattern) (ha : d84297 p = 1) (hb : d112238 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84229 q = 1) (hb : d99029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84229, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14225 q ha hb
    | true =>
      simp only [d84229, d99029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84230 q = 1) (hb : d99030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84230, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84230, d99030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84275 q = 1) (hb : d112216 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84275, d112216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84275, d112216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84276 q = 1) (hb : d112217 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84276, d112217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84276, d112217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84277 q = 1) (hb : d112218 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84277, d112218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84277, d112218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84297 q = 1) (hb : d112238 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84297, d112238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84297, d112238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20795 (p : Pattern) (ha : d84303 p = 1) (hb : d112244 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84255 q = 1) (hb : d112196 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84255, d112196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20785 q ha hb
    | true =>
      simp only [d84255, d112196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro243 q hb ha
  have h2 (q : Pattern) (ha : d84256 q = 1) (hb : d112197 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84256, d112197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84256, d112197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84257 q = 1) (hb : d112198 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84257, d112198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84257, d112198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84258 q = 1) (hb : d112199 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84258, d112199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84258, d112199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84262 q = 1) (hb : d112203 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84262, d112203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20786 q ha hb
    | true =>
      simp only [d84262, d112203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro245 q hb ha
  have h6 (q : Pattern) (ha : d84263 q = 1) (hb : d112204 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84263, d112204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84263, d112204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84264 q = 1) (hb : d112205 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84264, d112205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84264, d112205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84273 q = 1) (hb : d112214 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84273, d112214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20788 q ha hb
    | true =>
      simp only [d84273, d112214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20781 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d84235 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d84274 q = 1) (hb : d112215 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84274, d112215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84274, d112215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d84279 q = 1) (hb : d112220 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84279, d112220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20789 q ha hb
    | true =>
      simp only [d84279, d112220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d84280 q = 1) (hb : d112221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84280, d112221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d84280, d112221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d84281 q = 1) (hb : d112222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84281, d112222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84281, d112222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d84282 q = 1) (hb : d112223 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84282, d112223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84282, d112223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d84283 q = 1) (hb : d112224 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84283, d112224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84283, d112224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d84286 q = 1) (hb : d112227 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84286, d112227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20791 q ha hb
    | true =>
      simp only [d84286, d112227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro249 q hb ha
  have h17 (q : Pattern) (ha : d84287 q = 1) (hb : d112228 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84287, d112228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84287, d112228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d84288 q = 1) (hb : d112229 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84288, d112229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84288, d112229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d84289 q = 1) (hb : d112230 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84289, d112230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84289, d112230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d84291 q = 1) (hb : d112232 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84291, d112232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20792 q ha hb
    | true =>
      simp only [d84291, d112232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro251 q hb ha
  have h21 (q : Pattern) (ha : d84292 q = 1) (hb : d112233 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84292, d112233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84292, d112233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d84293 q = 1) (hb : d112234 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84293, d112234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d84293, d112234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d84295 q = 1) (hb : d112236 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84295, d112236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20793 q ha hb
    | true =>
      simp only [d84295, d112236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20783 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d84244 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d84296 q = 1) (hb : d112237 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84296, d112237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d84296, d112237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d84298 q = 1) (hb : d112239 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84298, d112239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20794 q ha hb
    | true =>
      simp only [d84298, d112239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d84299 q = 1) (hb : d112240 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84299, d112240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d84299, d112240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d84300 q = 1) (hb : d112241 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84300, d112241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d84300, d112241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d84301 q = 1) (hb : d112242 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84301, d112242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d84301, d112242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d84302 q = 1) (hb : d112243 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84302, d112243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d84302, d112243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d84303 q = 1) (hb : d112244 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84303, d112244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d84303, d112244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro20796 (p : Pattern) (ha : d84305 p = 1) (hb : d112246 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84235 q = 1) (hb : d112176 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84235, d112176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20781 q ha hb
    | true =>
      simp only [d84235, d112176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q hb ha
  have h2 (q : Pattern) (ha : d84236 q = 1) (hb : d112177 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84236, d112177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84236, d112177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84237 q = 1) (hb : d112178 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84237, d112178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84237, d112178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84238 q = 1) (hb : d112179 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84238, d112179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84238, d112179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84239 q = 1) (hb : d112180 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84239, d112180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84239, d112180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1827 q = 1) (hb : d53153 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, d53153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q ha hb
    | true =>
      simp only [d1827, d53153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1828 q = 1) (hb : d53154 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, d53154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1828, d53154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1829 q = 1) (hb : d53155 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, d53155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1829, d53155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1830 q = 1) (hb : d53156 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, d53156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, d53156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1831 q = 1) (hb : d53157 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, d53157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, d53157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84305 q = 1) (hb : d112246 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84305, d112246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84305, d112246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro20797 (p : Pattern) (ha : d84312 p = 1) (hb : d112253 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84295 q = 1) (hb : d112236 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84295, d112236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20793 q ha hb
    | true =>
      simp only [d84295, d112236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20783 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84244 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84296 q = 1) (hb : d112237 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84296, d112237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84296, d112237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d84298 q = 1) (hb : d112239 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84298, d112239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20794 q ha hb
    | true =>
      simp only [d84298, d112239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84299 q = 1) (hb : d112240 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84299, d112240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84299, d112240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84300 q = 1) (hb : d112241 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84300, d112241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84300, d112241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84310 q = 1) (hb : d112251 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84310, d112251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84310, d112251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84311 q = 1) (hb : d112252 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84311, d112252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84311, d112252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84312 q = 1) (hb : d112253 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84312, d112253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84312, d112253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro20798 (p : Pattern) (ha : d84319 p = 1) (hb : d112260 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1874 q = 1) (hb : d53200 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1874, d53200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro235 q ha hb
    | true =>
      simp only [d1874, d53200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro236 q ha hb
  have h2 (q : Pattern) (ha : d1875 q = 1) (hb : d53201 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1875, d53201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1875, d53201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1876 q = 1) (hb : d53202 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1876, d53202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1876, d53202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53207 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d9024 q = 1) (hb : d53208 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9024, d53208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9024, d53208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84318 q = 1) (hb : d112259 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84318, d112259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d84318, d112259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84319 q = 1) (hb : d112260 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84319, d112260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84319, d112260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro20799 (p : Pattern) (ha : d84329 p = 1) (hb : d112266 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84320 q = 1) (hb : d112261 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84320, d112261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20798 q ha hb
    | true =>
      simp only [d84320, d112261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84321 q = 1) (hb : d112262 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84321, d112262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84321, d112262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84324 q = 1) (hb : d99062 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84324, d99062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14234 q ha hb
    | true =>
      simp only [d84324, d99062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84325 q = 1) (hb : d99063 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84325, d99063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84325, d99063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84326 q = 1) (hb : d112263 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84326, d112263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84326, d112263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84327 q = 1) (hb : d112264 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84327, d112264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84327, d112264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84328 q = 1) (hb : d112265 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84328, d112265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84328, d112265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84329 q = 1) (hb : d112266 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84329, d112266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84329, d112266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20800 (p : Pattern) (ha : d84333 p = 1) (hb : d112270 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84324 q = 1) (hb : d99062 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84324, d99062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14234 q ha hb
    | true =>
      simp only [d84324, d99062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84325 q = 1) (hb : d99063 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84325, d99063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84325, d99063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1908 q = 1) (hb : d53234 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1908, d53234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro227 q ha hb
    | true =>
      simp only [d1908, d53234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1909 q = 1) (hb : d53235 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, d53235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1909, d53235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84330 q = 1) (hb : d112267 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84330, d112267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84330, d112267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84331 q = 1) (hb : d112268 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84331, d112268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84331, d112268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84332 q = 1) (hb : d112269 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84332, d112269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84332, d112269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84333 q = 1) (hb : d112270 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84333, d112270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84333, d112270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20801 (p : Pattern) (ha : d84340 p = 1) (hb : d112276 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84324 q = 1) (hb : d99062 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84324, d99062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14234 q ha hb
    | true =>
      simp only [d84324, d99062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84325 q = 1) (hb : d99063 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84325, d99063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84325, d99063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84337 q = 1) (hb : d112273 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84337, d112273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84337, d112273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84338 q = 1) (hb : d112274 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84338, d112274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84338, d112274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84339 q = 1) (hb : d112275 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84339, d112275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84339, d112275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84340 q = 1) (hb : d112276 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84340, d112276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84340, d112276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20802 (p : Pattern) (ha : d84346 p = 1) (hb : d112282 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84334 q = 1) (hb : d112271 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84334, d112271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20799 q ha hb
    | true =>
      simp only [d84334, d112271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20800 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84335 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84336 q = 1) (hb : d112272 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84336, d112272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84336, d112272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d84341 q = 1) (hb : d112277 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84341, d112277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20801 q ha hb
    | true =>
      simp only [d84341, d112277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84342 q = 1) (hb : d112278 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84342, d112278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84342, d112278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84343 q = 1) (hb : d112279 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84343, d112279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84343, d112279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84344 q = 1) (hb : d112280 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84344, d112280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84344, d112280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84345 q = 1) (hb : d112281 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84345, d112281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84345, d112281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84346 q = 1) (hb : d112282 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84346, d112282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84346, d112282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro20803 (p : Pattern) (ha : d84352 p = 1) (hb : d112288 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84241 q = 1) (hb : d112182 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84241, d112182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84241, d112182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20782 q ha hb
  have h2 (q : Pattern) (ha : d84242 q = 1) (hb : d112183 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84242, d112183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84242, d112183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84250 q = 1) (hb : d112191 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84250, d112191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20782 q ha hb
    | true =>
      simp only [d84250, d112191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20784 q ha hb
  have h4 (q : Pattern) (ha : d84251 q = 1) (hb : d112192 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84251, d112192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84251, d112192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84252 q = 1) (hb : d112193 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84252, d112193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84252, d112193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84304 q = 1) (hb : d112245 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84304, d112245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20790 q ha hb
    | true =>
      simp only [d84304, d112245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20795 q ha hb
  have h7 (q : Pattern) (ha : d84306 q = 1) (hb : d112247 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84306, d112247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20796 q ha hb
    | true =>
      simp only [d84306, d112247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro223 q hb ha
  have h8 (q : Pattern) (ha : d84307 q = 1) (hb : d112248 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84307, d112248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84307, d112248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84308 q = 1) (hb : d112249 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84308, d112249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84308, d112249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d84309 q = 1) (hb : d112250 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84309, d112250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84309, d112250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84313 q = 1) (hb : d112254 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84313, d112254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84313, d112254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20797 q ha hb
  have h12 (q : Pattern) (ha : d1848 q = 1) (hb : d53174 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1848, d53174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1848, d53174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro224 q ha hb
  have h13 (q : Pattern) (ha : d84314 q = 1) (hb : d112255 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84314, d112255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d84314, d112255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d84315 q = 1) (hb : d112256 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84315, d112256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84315, d112256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d84316 q = 1) (hb : d112257 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84316, d112257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d84316, d112257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d84317 q = 1) (hb : d112258 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84317, d112258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84317, d112258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d84347 q = 1) (hb : d112283 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84347, d112283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84347, d112283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20802 q ha hb
  have h18 (q : Pattern) (ha : d1981 q = 1) (hb : d53260 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1981, d53260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1981, d53260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro229 q ha hb
  have h19 (q : Pattern) (ha : d84348 q = 1) (hb : d112284 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84348, d112284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84348, d112284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d84349 q = 1) (hb : d112285 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84349, d112285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d84349, d112285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d84350 q = 1) (hb : d112286 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84350, d112286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d84350, d112286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d84351 q = 1) (hb : d112287 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84351, d112287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d84351, d112287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d84352 q = 1) (hb : d112288 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d84352, d112288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d84352, d112288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro20804 (p : Pattern) (ha : d84358 p = 1) (hb : d112294 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84353 q = 1) (hb : d112289 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d84353, d112289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84353, d112289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20803 q ha hb
  have h2 (q : Pattern) (ha : d84354 q = 1) (hb : d112290 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d84354, d112290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84354, d112290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84355 q = 1) (hb : d112291 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d84355, d112291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84355, d112291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d84356 q = 1) (hb : d112292 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d84356, d112292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84356, d112292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84357 q = 1) (hb : d112293 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d84357, d112293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84357, d112293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84358 q = 1) (hb : d112294 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d84358, d112294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84358, d112294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20805 (p : Pattern) (ha : d84370 p = 1) (hb : d112302 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84365 q = 1) (hb : d99092 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84365, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14246 q ha hb
    | true =>
      simp only [d84365, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84366 q = 1) (hb : d99093 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84366, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84366, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84367 q = 1) (hb : d112299 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84367, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84367, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84368 q = 1) (hb : d112300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84368, d112300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84368, d112300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84369 q = 1) (hb : d112301 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84369, d112301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84369, d112301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84370 q = 1) (hb : d112302 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84370, d112302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84370, d112302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20806 (p : Pattern) (ha : d84376 p = 1) (hb : d112308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84371 q = 1) (hb : d112303 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84371, d112303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20805 q ha hb
    | true =>
      simp only [d84371, d112303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q hb ha
  have h2 (q : Pattern) (ha : d84372 q = 1) (hb : d112304 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84372, d112304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84372, d112304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84373 q = 1) (hb : d112305 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84373, d112305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84373, d112305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84374 q = 1) (hb : d112306 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84374, d112306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84374, d112306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84375 q = 1) (hb : d112307 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84375, d112307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84375, d112307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84376 q = 1) (hb : d112308 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84376, d112308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84376, d112308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20807 (p : Pattern) (ha : d84379 p = 1) (hb : d112311 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84365 q = 1) (hb : d99092 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84365, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14246 q ha hb
    | true =>
      simp only [d84365, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84366 q = 1) (hb : d99093 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84366, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84366, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84367 q = 1) (hb : d112299 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84367, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84367, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84368 q = 1) (hb : d112300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84368, d112300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84368, d112300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84369 q = 1) (hb : d112301 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84369, d112301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84369, d112301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84379 q = 1) (hb : d112311 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84379, d112311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84379, d112311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20808 (p : Pattern) (ha : d84385 p = 1) (hb : d112317 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84371 q = 1) (hb : d112303 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84371, d112303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20805 q ha hb
    | true =>
      simp only [d84371, d112303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q hb ha
  have h2 (q : Pattern) (ha : d84372 q = 1) (hb : d112304 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84372, d112304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84372, d112304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84373 q = 1) (hb : d112305 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84373, d112305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84373, d112305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84374 q = 1) (hb : d112306 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84374, d112306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84374, d112306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84375 q = 1) (hb : d112307 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84375, d112307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84375, d112307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84380 q = 1) (hb : d112312 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84380, d112312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20807 q ha hb
    | true =>
      simp only [d84380, d112312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro279 q hb ha
  have h7 (q : Pattern) (ha : d84381 q = 1) (hb : d112313 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84381, d112313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84381, d112313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84382 q = 1) (hb : d112314 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84382, d112314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84382, d112314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d84383 q = 1) (hb : d112315 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84383, d112315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84383, d112315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84384 q = 1) (hb : d112316 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84384, d112316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84384, d112316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84385 q = 1) (hb : d112317 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84385, d112317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84385, d112317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro20809 (p : Pattern) (ha : d84390 p = 1) (hb : d112322 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84365 q = 1) (hb : d99092 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84365, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14246 q ha hb
    | true =>
      simp only [d84365, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84366 q = 1) (hb : d99093 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84366, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84366, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84367 q = 1) (hb : d112299 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84367, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84367, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84368 q = 1) (hb : d112300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84368, d112300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84368, d112300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84389 q = 1) (hb : d112321 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84389, d112321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84389, d112321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84390 q = 1) (hb : d112322 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84390, d112322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84390, d112322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20810 (p : Pattern) (ha : d84397 p = 1) (hb : d112329 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84365 q = 1) (hb : d99092 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84365, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14246 q ha hb
    | true =>
      simp only [d84365, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84366 q = 1) (hb : d99093 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84366, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84366, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84367 q = 1) (hb : d112299 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84367, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84367, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84395 q = 1) (hb : d112327 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84395, d112327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84395, d112327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84396 q = 1) (hb : d112328 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84396, d112328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84396, d112328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84397 q = 1) (hb : d112329 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84397, d112329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84397, d112329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20811 (p : Pattern) (ha : d84402 p = 1) (hb : d112334 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2150 q = 1) (hb : d53429 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2150, d53429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro290 q ha hb
    | true =>
      simp only [d2150, d53429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro269 q ha hb
  have h2 (q : Pattern) (ha : d2151 q = 1) (hb : d53430 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2151, d53430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2151, d53430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2152 q = 1) (hb : d53431 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2152, d53431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2152, d53431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53354 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d9117 q = 1) (hb : d53432 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9117, d53432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9117, d53432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84401 q = 1) (hb : d112333 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84401, d112333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d84401, d112333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84402 q = 1) (hb : d112334 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84402, d112334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84402, d112334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro20812 (p : Pattern) (ha : d84408 p = 1) (hb : d112340 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84403 q = 1) (hb : d112335 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84403, d112335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20811 q ha hb
    | true =>
      simp only [d84403, d112335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84404 q = 1) (hb : d112336 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84404, d112336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84404, d112336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84365 q = 1) (hb : d99092 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84365, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14246 q ha hb
    | true =>
      simp only [d84365, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84366 q = 1) (hb : d99093 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84366, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84366, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84405 q = 1) (hb : d112337 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84405, d112337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84405, d112337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84406 q = 1) (hb : d112338 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84406, d112338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84406, d112338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84407 q = 1) (hb : d112339 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84407, d112339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84407, d112339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84408 q = 1) (hb : d112340 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84408, d112340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84408, d112340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20813 (p : Pattern) (ha : d84414 p = 1) (hb : d112346 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84365 q = 1) (hb : d99092 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84365, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14246 q ha hb
    | true =>
      simp only [d84365, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84366 q = 1) (hb : d99093 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84366, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84366, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84411 q = 1) (hb : d112343 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84411, d112343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84411, d112343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84412 q = 1) (hb : d112344 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84412, d112344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84412, d112344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84413 q = 1) (hb : d112345 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84413, d112345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84413, d112345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84414 q = 1) (hb : d112346 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84414, d112346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84414, d112346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20814 (p : Pattern) (ha : d84420 p = 1) (hb : d112352 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84391 q = 1) (hb : d112323 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84391, d112323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20809 q ha hb
    | true =>
      simp only [d84391, d112323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro302 q hb ha
  have h2 (q : Pattern) (ha : d84392 q = 1) (hb : d112324 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84392, d112324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84392, d112324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84393 q = 1) (hb : d112325 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84393, d112325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84393, d112325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84394 q = 1) (hb : d112326 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84394, d112326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84394, d112326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84398 q = 1) (hb : d112330 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84398, d112330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20810 q ha hb
    | true =>
      simp only [d84398, d112330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro304 q hb ha
  have h6 (q : Pattern) (ha : d84399 q = 1) (hb : d112331 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84399, d112331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84399, d112331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84400 q = 1) (hb : d112332 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84400, d112332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84400, d112332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84409 q = 1) (hb : d112341 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84409, d112341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20812 q ha hb
    | true =>
      simp only [d84409, d112341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20805 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d84371 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d84410 q = 1) (hb : d112342 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84410, d112342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84410, d112342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d84415 q = 1) (hb : d112347 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84415, d112347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20813 q ha hb
    | true =>
      simp only [d84415, d112347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d84416 q = 1) (hb : d112348 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84416, d112348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d84416, d112348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d84417 q = 1) (hb : d112349 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84417, d112349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84417, d112349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d84418 q = 1) (hb : d112350 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84418, d112350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84418, d112350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d84419 q = 1) (hb : d112351 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84419, d112351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84419, d112351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d84420 q = 1) (hb : d112352 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84420, d112352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84420, d112352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro20815 (p : Pattern) (ha : d84421 p = 1) (hb : d112353 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84365 q = 1) (hb : d99092 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84365, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14246 q ha hb
    | true =>
      simp only [d84365, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84366 q = 1) (hb : d99093 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84366, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84366, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84367 q = 1) (hb : d112299 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84367, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84367, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84368 q = 1) (hb : d112300 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84368, d112300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84368, d112300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84389 q = 1) (hb : d112321 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84389, d112321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84389, d112321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84421 q = 1) (hb : d112353 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84421, d112353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84421, d112353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20816 (p : Pattern) (ha : d84426 p = 1) (hb : d112358 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84365 q = 1) (hb : d99092 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84365, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14246 q ha hb
    | true =>
      simp only [d84365, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84366 q = 1) (hb : d99093 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84366, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84366, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84367 q = 1) (hb : d112299 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84367, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84367, d112299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84395 q = 1) (hb : d112327 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84395, d112327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84395, d112327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84396 q = 1) (hb : d112328 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84396, d112328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84396, d112328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84426 q = 1) (hb : d112358 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84426, d112358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84426, d112358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20817 (p : Pattern) (ha : d84430 p = 1) (hb : d112362 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84403 q = 1) (hb : d112335 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84403, d112335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20811 q ha hb
    | true =>
      simp only [d84403, d112335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84404 q = 1) (hb : d112336 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84404, d112336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84404, d112336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84365 q = 1) (hb : d99092 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84365, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14246 q ha hb
    | true =>
      simp only [d84365, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84366 q = 1) (hb : d99093 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84366, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84366, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84405 q = 1) (hb : d112337 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84405, d112337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84405, d112337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84406 q = 1) (hb : d112338 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84406, d112338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84406, d112338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84407 q = 1) (hb : d112339 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84407, d112339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84407, d112339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84430 q = 1) (hb : d112362 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84430, d112362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84430, d112362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20818 (p : Pattern) (ha : d84433 p = 1) (hb : d112365 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84365 q = 1) (hb : d99092 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84365, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14246 q ha hb
    | true =>
      simp only [d84365, d99092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84366 q = 1) (hb : d99093 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84366, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84366, d99093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84411 q = 1) (hb : d112343 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84411, d112343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84411, d112343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84412 q = 1) (hb : d112344 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84412, d112344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84412, d112344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84413 q = 1) (hb : d112345 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84413, d112345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84413, d112345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84433 q = 1) (hb : d112365 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84433, d112365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84433, d112365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20819 (p : Pattern) (ha : d84439 p = 1) (hb : d112371 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84391 q = 1) (hb : d112323 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84391, d112323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20809 q ha hb
    | true =>
      simp only [d84391, d112323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro302 q hb ha
  have h2 (q : Pattern) (ha : d84392 q = 1) (hb : d112324 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84392, d112324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84392, d112324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84393 q = 1) (hb : d112325 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84393, d112325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84393, d112325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84394 q = 1) (hb : d112326 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84394, d112326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84394, d112326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84398 q = 1) (hb : d112330 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84398, d112330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20810 q ha hb
    | true =>
      simp only [d84398, d112330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro304 q hb ha
  have h6 (q : Pattern) (ha : d84399 q = 1) (hb : d112331 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84399, d112331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84399, d112331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84400 q = 1) (hb : d112332 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84400, d112332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84400, d112332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84409 q = 1) (hb : d112341 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84409, d112341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20812 q ha hb
    | true =>
      simp only [d84409, d112341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20805 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d84371 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d84410 q = 1) (hb : d112342 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84410, d112342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84410, d112342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d84415 q = 1) (hb : d112347 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84415, d112347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20813 q ha hb
    | true =>
      simp only [d84415, d112347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d84416 q = 1) (hb : d112348 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84416, d112348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d84416, d112348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d84417 q = 1) (hb : d112349 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84417, d112349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84417, d112349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d84418 q = 1) (hb : d112350 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84418, d112350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84418, d112350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d84419 q = 1) (hb : d112351 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84419, d112351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84419, d112351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d84422 q = 1) (hb : d112354 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84422, d112354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20815 q ha hb
    | true =>
      simp only [d84422, d112354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro308 q hb ha
  have h17 (q : Pattern) (ha : d84423 q = 1) (hb : d112355 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84423, d112355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84423, d112355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d84424 q = 1) (hb : d112356 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84424, d112356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84424, d112356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d84425 q = 1) (hb : d112357 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84425, d112357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84425, d112357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d84427 q = 1) (hb : d112359 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84427, d112359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20816 q ha hb
    | true =>
      simp only [d84427, d112359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro310 q hb ha
  have h21 (q : Pattern) (ha : d84428 q = 1) (hb : d112360 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84428, d112360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84428, d112360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d84429 q = 1) (hb : d112361 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84429, d112361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d84429, d112361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d84431 q = 1) (hb : d112363 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84431, d112363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20817 q ha hb
    | true =>
      simp only [d84431, d112363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20807 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d84380 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d84432 q = 1) (hb : d112364 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84432, d112364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d84432, d112364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d84434 q = 1) (hb : d112366 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84434, d112366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20818 q ha hb
    | true =>
      simp only [d84434, d112366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d84435 q = 1) (hb : d112367 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84435, d112367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d84435, d112367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d84436 q = 1) (hb : d112368 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84436, d112368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d84436, d112368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d84437 q = 1) (hb : d112369 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84437, d112369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d84437, d112369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d84438 q = 1) (hb : d112370 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84438, d112370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d84438, d112370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d84439 q = 1) (hb : d112371 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84439, d112371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d84439, d112371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro20820 (p : Pattern) (ha : d84441 p = 1) (hb : d112373 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84371 q = 1) (hb : d112303 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84371, d112303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20805 q ha hb
    | true =>
      simp only [d84371, d112303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q hb ha
  have h2 (q : Pattern) (ha : d84372 q = 1) (hb : d112304 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84372, d112304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84372, d112304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84373 q = 1) (hb : d112305 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84373, d112305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84373, d112305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84374 q = 1) (hb : d112306 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84374, d112306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84374, d112306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84375 q = 1) (hb : d112307 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84375, d112307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84375, d112307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2305 q = 1) (hb : d53470 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, d53470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q ha hb
    | true =>
      simp only [d2305, d53470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2306 q = 1) (hb : d53471 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, d53471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2306, d53471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2307 q = 1) (hb : d53472 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, d53472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2307, d53472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2308 q = 1) (hb : d53473 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, d53473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2308, d53473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2309 q = 1) (hb : d53474 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, d53474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, d53474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84441 q = 1) (hb : d112373 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84441, d112373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84441, d112373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro20821 (p : Pattern) (ha : d84448 p = 1) (hb : d112380 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84431 q = 1) (hb : d112363 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84431, d112363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20817 q ha hb
    | true =>
      simp only [d84431, d112363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20807 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84380 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84432 q = 1) (hb : d112364 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84432, d112364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84432, d112364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d84434 q = 1) (hb : d112366 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84434, d112366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20818 q ha hb
    | true =>
      simp only [d84434, d112366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84435 q = 1) (hb : d112367 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84435, d112367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84435, d112367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84436 q = 1) (hb : d112368 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84436, d112368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84436, d112368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84446 q = 1) (hb : d112378 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84446, d112378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84446, d112378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84447 q = 1) (hb : d112379 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84447, d112379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84447, d112379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84448 q = 1) (hb : d112380 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84448, d112380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84448, d112380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro20822 (p : Pattern) (ha : d84455 p = 1) (hb : d112387 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2352 q = 1) (hb : d53517 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2352, d53517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro294 q ha hb
    | true =>
      simp only [d2352, d53517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro295 q ha hb
  have h2 (q : Pattern) (ha : d2353 q = 1) (hb : d53518 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2353, d53518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2353, d53518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2354 q = 1) (hb : d53519 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2354, d53519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2354, d53519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d53524 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d9193 q = 1) (hb : d53525 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9193, d53525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9193, d53525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84454 q = 1) (hb : d112386 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d84454, d112386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d84454, d112386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84455 q = 1) (hb : d112387 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d84455, d112387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84455, d112387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro20823 (p : Pattern) (ha : d84465 p = 1) (hb : d112393 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84456 q = 1) (hb : d112388 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84456, d112388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20822 q ha hb
    | true =>
      simp only [d84456, d112388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84457 q = 1) (hb : d112389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84457, d112389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84457, d112389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84460 q = 1) (hb : d99125 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84460, d99125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14255 q ha hb
    | true =>
      simp only [d84460, d99125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84461 q = 1) (hb : d99126 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84461, d99126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84461, d99126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84462 q = 1) (hb : d112390 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84462, d112390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84462, d112390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84463 q = 1) (hb : d112391 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84463, d112391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84463, d112391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84464 q = 1) (hb : d112392 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84464, d112392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84464, d112392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84465 q = 1) (hb : d112393 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84465, d112393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84465, d112393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20824 (p : Pattern) (ha : d84469 p = 1) (hb : d112397 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84460 q = 1) (hb : d99125 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84460, d99125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14255 q ha hb
    | true =>
      simp only [d84460, d99125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84461 q = 1) (hb : d99126 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84461, d99126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84461, d99126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2386 q = 1) (hb : d53551 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2386, d53551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro286 q ha hb
    | true =>
      simp only [d2386, d53551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2387 q = 1) (hb : d53552 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2387, d53552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2387, d53552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84466 q = 1) (hb : d112394 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84466, d112394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84466, d112394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84467 q = 1) (hb : d112395 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84467, d112395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84467, d112395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d84468 q = 1) (hb : d112396 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84468, d112396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84468, d112396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d84469 q = 1) (hb : d112397 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84469, d112397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84469, d112397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro20825 (p : Pattern) (ha : d84476 p = 1) (hb : d112403 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84460 q = 1) (hb : d99125 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d84460, d99125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14255 q ha hb
    | true =>
      simp only [d84460, d99125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84461 q = 1) (hb : d99126 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d84461, d99126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84461, d99126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84473 q = 1) (hb : d112400 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d84473, d112400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84473, d112400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84474 q = 1) (hb : d112401 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d84474, d112401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84474, d112401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84475 q = 1) (hb : d112402 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d84475, d112402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84475, d112402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84476 q = 1) (hb : d112403 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d84476, d112403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84476, d112403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20826 (p : Pattern) (ha : d84482 p = 1) (hb : d112409 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84470 q = 1) (hb : d112398 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84470, d112398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20823 q ha hb
    | true =>
      simp only [d84470, d112398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20824 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84471 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84472 q = 1) (hb : d112399 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84472, d112399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84472, d112399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d84477 q = 1) (hb : d112404 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84477, d112404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20825 q ha hb
    | true =>
      simp only [d84477, d112404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84478 q = 1) (hb : d112405 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84478, d112405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84478, d112405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84479 q = 1) (hb : d112406 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84479, d112406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84479, d112406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84480 q = 1) (hb : d112407 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84480, d112407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84480, d112407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84481 q = 1) (hb : d112408 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84481, d112408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84481, d112408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84482 q = 1) (hb : d112409 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84482, d112409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84482, d112409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro20827 (p : Pattern) (ha : d84488 p = 1) (hb : d112415 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84377 q = 1) (hb : d112309 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84377, d112309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84377, d112309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20806 q ha hb
  have h2 (q : Pattern) (ha : d84378 q = 1) (hb : d112310 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84378, d112310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84378, d112310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84386 q = 1) (hb : d112318 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84386, d112318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20806 q ha hb
    | true =>
      simp only [d84386, d112318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20808 q ha hb
  have h4 (q : Pattern) (ha : d84387 q = 1) (hb : d112319 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84387, d112319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84387, d112319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84388 q = 1) (hb : d112320 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84388, d112320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84388, d112320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84440 q = 1) (hb : d112372 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84440, d112372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20814 q ha hb
    | true =>
      simp only [d84440, d112372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20819 q ha hb
  have h7 (q : Pattern) (ha : d84442 q = 1) (hb : d112374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84442, d112374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20820 q ha hb
    | true =>
      simp only [d84442, d112374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro282 q hb ha
  have h8 (q : Pattern) (ha : d84443 q = 1) (hb : d112375 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84443, d112375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84443, d112375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84444 q = 1) (hb : d112376 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84444, d112376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84444, d112376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d84445 q = 1) (hb : d112377 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84445, d112377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84445, d112377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84449 q = 1) (hb : d112381 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84449, d112381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84449, d112381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20821 q ha hb
  have h12 (q : Pattern) (ha : d2326 q = 1) (hb : d53491 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2326, d53491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2326, d53491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro283 q ha hb
  have h13 (q : Pattern) (ha : d84450 q = 1) (hb : d112382 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84450, d112382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d84450, d112382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d84451 q = 1) (hb : d112383 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84451, d112383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84451, d112383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d84452 q = 1) (hb : d112384 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84452, d112384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d84452, d112384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d84453 q = 1) (hb : d112385 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84453, d112385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84453, d112385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d84483 q = 1) (hb : d112410 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84483, d112410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84483, d112410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20826 q ha hb
  have h18 (q : Pattern) (ha : d2459 q = 1) (hb : d53577 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2459, d53577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2459, d53577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro288 q ha hb
  have h19 (q : Pattern) (ha : d84484 q = 1) (hb : d112411 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84484, d112411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84484, d112411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d84485 q = 1) (hb : d112412 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84485, d112412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d84485, d112412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d84486 q = 1) (hb : d112413 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84486, d112413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d84486, d112413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d84487 q = 1) (hb : d112414 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84487, d112414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d84487, d112414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d84488 q = 1) (hb : d112415 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d84488, d112415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d84488, d112415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro20828 (p : Pattern) (ha : d84494 p = 1) (hb : d112421 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84489 q = 1) (hb : d112416 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d84489, d112416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84489, d112416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20827 q ha hb
  have h2 (q : Pattern) (ha : d84490 q = 1) (hb : d112417 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d84490, d112417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84490, d112417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84491 q = 1) (hb : d112418 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d84491, d112418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84491, d112418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d84492 q = 1) (hb : d112419 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d84492, d112419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84492, d112419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84493 q = 1) (hb : d112420 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d84493, d112420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84493, d112420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84494 q = 1) (hb : d112421 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d84494, d112421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84494, d112421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20829 (p : Pattern) (ha : d84500 p = 1) (hb : d112427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d83957 q = 1) (hb : d111920 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d83957, d111920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20708 q ha hb
    | true =>
      simp only [d83957, d111920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20732 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84090 q = 1) (hb : d112044 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d84090, d112044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84090, d112044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20756 q ha hb
  have h3 (q : Pattern) (ha : d84091 q = 1) (hb : d112045 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d84091, d112045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d84091, d112045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d84224 q = 1) (hb : d112169 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d84224, d112169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84224, d112169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20780 q ha hb
  have h5 (q : Pattern) (ha : d84225 q = 1) (hb : d112170 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d84225, d112170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84225, d112170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84226 q = 1) (hb : d112171 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d84226, d112171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84226, d112171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84359 q = 1) (hb : d112295 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d84359, d112295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84359, d112295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20804 q ha hb
  have h8 (q : Pattern) (ha : d84360 q = 1) (hb : d112296 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d84360, d112296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84360, d112296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84361 q = 1) (hb : d112297 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d84361, d112297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84361, d112297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84362 q = 1) (hb : d112298 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d84362, d112298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84362, d112298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84495 q = 1) (hb : d112422 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d84495, d112422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84495, d112422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20828 q ha hb
  have h12 (q : Pattern) (ha : d84496 q = 1) (hb : d112423 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d84496, d112423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84496, d112423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d84497 q = 1) (hb : d112424 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d84497, d112424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84497, d112424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d84498 q = 1) (hb : d112425 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d84498, d112425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84498, d112425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d84499 q = 1) (hb : d112426 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d84499, d112426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84499, d112426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d84500 q = 1) (hb : d112427 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d84500, d112427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d84500, d112427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro20830 (p : Pattern) (ha : d84506 p = 1) (hb : d112433 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84501 q = 1) (hb : d112428 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d84501, d112428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20829 q ha hb
    | true =>
      simp only [d84501, d112428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84502 q = 1) (hb : d112429 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d84502, d112429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84502, d112429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84503 q = 1) (hb : d112430 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d84503, d112430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84503, d112430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84504 q = 1) (hb : d112431 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d84504, d112431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84504, d112431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84505 q = 1) (hb : d112432 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d84505, d112432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84505, d112432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84506 q = 1) (hb : d112433 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d84506, d112433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84506, d112433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20831 (p : Pattern) (ha : d84512 p = 1) (hb : d112439 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84507 q = 1) (hb : d112434 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d84507, d112434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20830 q ha hb
    | true =>
      simp only [d84507, d112434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84508 q = 1) (hb : d112435 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d84508, d112435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84508, d112435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84509 q = 1) (hb : d112436 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d84509, d112436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84509, d112436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84510 q = 1) (hb : d112437 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d84510, d112437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84510, d112437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84511 q = 1) (hb : d112438 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d84511, d112438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84511, d112438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84512 q = 1) (hb : d112439 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d84512, d112439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84512, d112439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20832 (p : Pattern) (ha : d84518 p = 1) (hb : d112445 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84513 q = 1) (hb : d112440 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d84513, d112440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20831 q ha hb
    | true =>
      simp only [d84513, d112440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84514 q = 1) (hb : d112441 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d84514, d112441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84514, d112441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84515 q = 1) (hb : d112442 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d84515, d112442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84515, d112442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84516 q = 1) (hb : d112443 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d84516, d112443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84516, d112443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84517 q = 1) (hb : d112444 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d84517, d112444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84517, d112444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84518 q = 1) (hb : d112445 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d84518, d112445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84518, d112445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20833 (p : Pattern) (ha : d84524 p = 1) (hb : d112451 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84519 q = 1) (hb : d112446 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d84519, d112446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20832 q ha hb
    | true =>
      simp only [d84519, d112446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84520 q = 1) (hb : d112447 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d84520, d112447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84520, d112447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84521 q = 1) (hb : d112448 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d84521, d112448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84521, d112448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84522 q = 1) (hb : d112449 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d84522, d112449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84522, d112449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84523 q = 1) (hb : d112450 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d84523, d112450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84523, d112450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84524 q = 1) (hb : d112451 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d84524, d112451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84524, d112451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20834 (p : Pattern) (ha : d84530 p = 1) (hb : d112457 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84525 q = 1) (hb : d112452 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d84525, d112452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20833 q ha hb
    | true =>
      simp only [d84525, d112452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84526 q = 1) (hb : d112453 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d84526, d112453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84526, d112453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84527 q = 1) (hb : d112454 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d84527, d112454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84527, d112454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84528 q = 1) (hb : d112455 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d84528, d112455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84528, d112455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84529 q = 1) (hb : d112456 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d84529, d112456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84529, d112456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84530 q = 1) (hb : d112457 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d84530, d112457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84530, d112457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20835 (p : Pattern) (ha : d84536 p = 1) (hb : d112463 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84531 q = 1) (hb : d112458 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d84531, d112458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20834 q ha hb
    | true =>
      simp only [d84531, d112458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84532 q = 1) (hb : d112459 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d84532, d112459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84532, d112459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84533 q = 1) (hb : d112460 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d84533, d112460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84533, d112460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84534 q = 1) (hb : d112461 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d84534, d112461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84534, d112461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84535 q = 1) (hb : d112462 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d84535, d112462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84535, d112462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84536 q = 1) (hb : d112463 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d84536, d112463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84536, d112463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20836 (p : Pattern) (ha : d84542 p = 1) (hb : d112469 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84537 q = 1) (hb : d112464 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d84537, d112464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20835 q ha hb
    | true =>
      simp only [d84537, d112464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84538 q = 1) (hb : d112465 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d84538, d112465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84538, d112465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84539 q = 1) (hb : d112466 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d84539, d112466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84539, d112466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84540 q = 1) (hb : d112467 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d84540, d112467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84540, d112467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84541 q = 1) (hb : d112468 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d84541, d112468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84541, d112468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84542 q = 1) (hb : d112469 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d84542, d112469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84542, d112469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20837 (p : Pattern) (ha : d92315 p = 1) (hb : d94521 p = 1) : d112472 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d92315 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8246 q = 1) (hb : d92315 q = 1) : d111675 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8246, d111675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20509 q ha hb
    | true =>
      simp only [d8246, d111675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8292 q = 1) (hb : d92315 q = 1) : d111721 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8292, d111721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8292, d111721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8293 q = 1) (hb : d92315 q = 1) : d111722 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8293, d111722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8293, d111722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8294 q = 1) (hb : d92315 q = 1) : d111723 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8294, d111723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8294, d111723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8295 q = 1) (hb : d92315 q = 1) : d111724 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8295, d111724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8295, d111724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94521 q = 1) : d112472 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94521, d112472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94521, d112472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro20838 (p : Pattern) (ha : d92315 p = 1) (hb : d94531 p = 1) : d112482 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d92315 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8268 q = 1) (hb : d92315 q = 1) : d111697 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8268, d111697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20512 q ha hb
    | true =>
      simp only [d8268, d111697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94527 q = 1) : d112478 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94527, d112478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94527, d112478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94528 q = 1) : d112479 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94528, d112479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94528, d112479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94529 q = 1) : d112480 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94529, d112480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94529, d112480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94530 q = 1) : d112481 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94530, d112481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94530, d112481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94531 q = 1) : d112482 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94531, d112482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94531, d112482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro20839 (p : Pattern) (ha : d92315 p = 1) (hb : d94537 p = 1) : d112488 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8297 q = 1) (hb : d92315 q = 1) : d111726 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8297, d111726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20515 q ha hb
    | true =>
      simp only [d8297, d111726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20516 q ha hb
  have h2 (q : Pattern) (ha : d8298 q = 1) (hb : d92315 q = 1) : d111727 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8298, d111727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8298, d111727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94519 q = 1) : d112470 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94519, d112470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94519, d112470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94520 q = 1) : d112471 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94520, d112471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94520, d112471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94522 q = 1) : d112473 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94522, d112473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94522, d112473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20837 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94523 q = 1) : d112474 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94523, d112474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94523, d112474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94524 q = 1) : d112475 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94524, d112475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94524, d112475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92315 q = 1) (hb : d94525 q = 1) : d112476 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94525, d112476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94525, d112476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92315 q = 1) (hb : d94526 q = 1) : d112477 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94526, d112477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94526, d112477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92315 q = 1) (hb : d94532 q = 1) : d112483 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94532, d112483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94532, d112483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20838 q ha hb
  have h11 (q : Pattern) (ha : d92315 q = 1) (hb : d94533 q = 1) : d112484 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94533, d112484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94533, d112484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92315 q = 1) (hb : d94534 q = 1) : d112485 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94534, d112485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94534, d112485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92315 q = 1) (hb : d94535 q = 1) : d112486 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94535, d112486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94535, d112486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d92315 q = 1) (hb : d94536 q = 1) : d112487 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94536, d112487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94536, d112487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d92315 q = 1) (hb : d94537 q = 1) : d112488 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94537, d112488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94537, d112488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro20840 (p : Pattern) (ha : d92315 p = 1) (hb : d94543 p = 1) : d112494 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d92315 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94538 q = 1) : d112489 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94538, d112489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94538, d112489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20839 q ha hb
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94539 q = 1) : d112490 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94539, d112490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94539, d112490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94540 q = 1) : d112491 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94540, d112491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94540, d112491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94541 q = 1) : d112492 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94541, d112492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94541, d112492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94542 q = 1) : d112493 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94542, d112493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94542, d112493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94543 q = 1) : d112494 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94543, d112494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94543, d112494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro20841 (p : Pattern) (ha : d92315 p = 1) (hb : d94546 p = 1) : d112497 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d501 q = 1) (hb : d92315 q = 1) : d501 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8430 q = 1) (hb : d92315 q = 1) : d111814 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8430, d111814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20538 q ha hb
    | true =>
      simp only [d8430, d111814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8431 q = 1) (hb : d92315 q = 1) : d111815 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8431, d111815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8431, d111815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8432 q = 1) (hb : d92315 q = 1) : d111816 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8432, d111816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8432, d111816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8433 q = 1) (hb : d92315 q = 1) : d111817 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8433, d111817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8433, d111817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8434 q = 1) (hb : d92315 q = 1) : d111818 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8434, d111818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8434, d111818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94546 q = 1) : d112497 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94546, d112497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94546, d112497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro20842 (p : Pattern) (ha : d92315 p = 1) (hb : d94555 p = 1) : d111786 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8378 q = 1) (hb : d92315 q = 1) : d98879 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8378, d98879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20530 q ha hb
    | true =>
      simp only [d8378, d98879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8379 q = 1) (hb : d92315 q = 1) : d98880 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8379, d98880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8379, d98880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d685 q = 1) (hb : d92315 q = 1) : d685 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94552 q = 1) : d111783 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d94552, d111783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94552, d111783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94553 q = 1) : d111784 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d94553, d111784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94553, d111784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94554 q = 1) : d111785 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d94554, d111785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94554, d111785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94555 q = 1) : d111786 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d94555, d111786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94555, d111786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro20843 (p : Pattern) (ha : d92315 p = 1) (hb : d94561 p = 1) : d112508 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d730 q = 1) (hb : d92315 q = 1) : d730 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94556 q = 1) : d112503 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d94556, d112503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20842 q ha hb
    | true =>
      simp only [d94556, d112503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94557 q = 1) : d112504 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94557, d112504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94557, d112504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94558 q = 1) : d112505 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94558, d112505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94558, d112505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94559 q = 1) : d112506 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94559, d112506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94559, d112506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94560 q = 1) : d112507 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94560, d112507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94560, d112507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94561 q = 1) : d112508 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94561, d112508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94561, d112508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro20844 (p : Pattern) (ha : d92315 p = 1) (hb : d94567 p = 1) : d112514 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8436 q = 1) (hb : d92315 q = 1) : d111820 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8436, d111820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20537 q ha hb
    | true =>
      simp only [d8436, d111820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20539 q ha hb
  have h2 (q : Pattern) (ha : d8437 q = 1) (hb : d92315 q = 1) : d111821 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8437, d111821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8437, d111821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94544 q = 1) : d112495 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94544, d112495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94544, d112495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94545 q = 1) : d112496 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94545, d112496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94545, d112496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94547 q = 1) : d112498 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94547, d112498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94547, d112498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20841 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94548 q = 1) : d112499 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94548, d112499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94548, d112499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94549 q = 1) : d112500 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94549, d112500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94549, d112500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92315 q = 1) (hb : d94550 q = 1) : d112501 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94550, d112501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94550, d112501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92315 q = 1) (hb : d94551 q = 1) : d112502 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94551, d112502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94551, d112502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92315 q = 1) (hb : d94562 q = 1) : d112509 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94562, d112509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94562, d112509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20843 q ha hb
  have h11 (q : Pattern) (ha : d92315 q = 1) (hb : d94563 q = 1) : d112510 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94563, d112510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94563, d112510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92315 q = 1) (hb : d94564 q = 1) : d112511 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94564, d112511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94564, d112511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92315 q = 1) (hb : d94565 q = 1) : d112512 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94565, d112512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94565, d112512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d92315 q = 1) (hb : d94566 q = 1) : d112513 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94566, d112513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94566, d112513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d92315 q = 1) (hb : d94567 q = 1) : d112514 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94567, d112514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94567, d112514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro20845 (p : Pattern) (ha : d92315 p = 1) (hb : d94573 p = 1) : d112520 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92315 q = 1) (hb : d94568 q = 1) : d112515 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94568, d112515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94568, d112515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20844 q ha hb
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94569 q = 1) : d112516 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94569, d112516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94569, d112516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94570 q = 1) : d112517 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94570, d112517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94570, d112517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94571 q = 1) : d112518 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94571, d112518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94571, d112518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94572 q = 1) : d112519 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94572, d112519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94572, d112519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94573 q = 1) : d112520 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94573, d112520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94573, d112520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20846 (p : Pattern) (ha : d92315 p = 1) (hb : d94577 p = 1) : d112524 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d793 q = 1) (hb : d92315 q = 1) : d793 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8592 q = 1) (hb : d92315 q = 1) : d111934 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8592, d111934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20565 q ha hb
    | true =>
      simp only [d8592, d111934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8593 q = 1) (hb : d92315 q = 1) : d111935 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8593, d111935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8593, d111935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8594 q = 1) (hb : d92315 q = 1) : d111936 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8594, d111936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8594, d111936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8595 q = 1) (hb : d92315 q = 1) : d111937 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8595, d111937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8595, d111937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8596 q = 1) (hb : d92315 q = 1) : d111938 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8596, d111938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8596, d111938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94577 q = 1) : d112524 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94577, d112524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94577, d112524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro20847 (p : Pattern) (ha : d92315 p = 1) (hb : d94586 p = 1) : d112019 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8716 q = 1) (hb : d92315 q = 1) : d98939 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8716, d98939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20585 q ha hb
    | true =>
      simp only [d8716, d98939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8717 q = 1) (hb : d92315 q = 1) : d98940 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8717, d98940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8717, d98940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1007 q = 1) (hb : d92315 q = 1) : d1007 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94583 q = 1) : d112016 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d94583, d112016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94583, d112016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94584 q = 1) : d112017 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d94584, d112017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94584, d112017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94585 q = 1) : d112018 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d94585, d112018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94585, d112018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94586 q = 1) : d112019 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d94586, d112019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94586, d112019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro20848 (p : Pattern) (ha : d92315 p = 1) (hb : d94592 p = 1) : d112535 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1063 q = 1) (hb : d92315 q = 1) : d1063 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94587 q = 1) : d112530 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d94587, d112530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20847 q ha hb
    | true =>
      simp only [d94587, d112530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94588 q = 1) : d112531 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94588, d112531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94588, d112531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94589 q = 1) : d112532 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94589, d112532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94589, d112532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94590 q = 1) : d112533 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94590, d112533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94590, d112533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94591 q = 1) : d112534 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94591, d112534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94591, d112534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94592 q = 1) : d112535 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94592, d112535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94592, d112535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro20849 (p : Pattern) (ha : d92315 p = 1) (hb : d94598 p = 1) : d112541 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8598 q = 1) (hb : d92315 q = 1) : d111940 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8598, d111940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20564 q ha hb
    | true =>
      simp only [d8598, d111940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20566 q ha hb
  have h2 (q : Pattern) (ha : d8599 q = 1) (hb : d92315 q = 1) : d111941 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8599, d111941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8599, d111941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94575 q = 1) : d112522 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94575, d112522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94575, d112522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94576 q = 1) : d112523 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94576, d112523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94576, d112523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94578 q = 1) : d112525 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94578, d112525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94578, d112525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20846 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94579 q = 1) : d112526 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94579, d112526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94579, d112526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94580 q = 1) : d112527 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94580, d112527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94580, d112527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92315 q = 1) (hb : d94581 q = 1) : d112528 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94581, d112528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94581, d112528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92315 q = 1) (hb : d94582 q = 1) : d112529 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94582, d112529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94582, d112529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92315 q = 1) (hb : d94593 q = 1) : d112536 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94593, d112536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94593, d112536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20848 q ha hb
  have h11 (q : Pattern) (ha : d92315 q = 1) (hb : d94594 q = 1) : d112537 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94594, d112537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94594, d112537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92315 q = 1) (hb : d94595 q = 1) : d112538 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94595, d112538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94595, d112538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92315 q = 1) (hb : d94596 q = 1) : d112539 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94596, d112539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94596, d112539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d92315 q = 1) (hb : d94597 q = 1) : d112540 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94597, d112540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94597, d112540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d92315 q = 1) (hb : d94598 q = 1) : d112541 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94598, d112541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94598, d112541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro20850 (p : Pattern) (ha : d92315 p = 1) (hb : d94604 p = 1) : d112547 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92315 q = 1) (hb : d94599 q = 1) : d112542 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94599, d112542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94599, d112542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20849 q ha hb
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94600 q = 1) : d112543 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94600, d112543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94600, d112543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94601 q = 1) : d112544 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94601, d112544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94601, d112544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94602 q = 1) : d112545 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94602, d112545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94602, d112545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94603 q = 1) : d112546 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94603, d112546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94603, d112546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94604 q = 1) : d112547 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94604, d112547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94604, d112547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20851 (p : Pattern) (ha : d92315 p = 1) (hb : d94609 p = 1) : d112552 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1172 q = 1) (hb : d92315 q = 1) : d1172 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8759 q = 1) (hb : d92315 q = 1) : d112059 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8759, d112059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20593 q ha hb
    | true =>
      simp only [d8759, d112059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8760 q = 1) (hb : d92315 q = 1) : d112060 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8760, d112060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8760, d112060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8761 q = 1) (hb : d92315 q = 1) : d112061 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8761, d112061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8761, d112061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8762 q = 1) (hb : d92315 q = 1) : d112062 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8762, d112062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8762, d112062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8763 q = 1) (hb : d92315 q = 1) : d112063 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8763, d112063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8763, d112063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94609 q = 1) : d112552 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94609, d112552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94609, d112552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro20852 (p : Pattern) (ha : d92315 p = 1) (hb : d94618 p = 1) : d112144 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8883 q = 1) (hb : d92315 q = 1) : d99000 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8883, d99000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20613 q ha hb
    | true =>
      simp only [d8883, d99000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8884 q = 1) (hb : d92315 q = 1) : d99001 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8884, d99001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8884, d99001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1432 q = 1) (hb : d92315 q = 1) : d1432 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94615 q = 1) : d112141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d94615, d112141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94615, d112141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94616 q = 1) : d112142 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d94616, d112142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94616, d112142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94617 q = 1) : d112143 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d94617, d112143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94617, d112143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94618 q = 1) : d112144 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d94618, d112144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94618, d112144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro20853 (p : Pattern) (ha : d92315 p = 1) (hb : d94624 p = 1) : d112563 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1497 q = 1) (hb : d92315 q = 1) : d1497 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94619 q = 1) : d112558 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d94619, d112558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20852 q ha hb
    | true =>
      simp only [d94619, d112558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94620 q = 1) : d112559 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94620, d112559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94620, d112559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94621 q = 1) : d112560 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94621, d112560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94621, d112560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94622 q = 1) : d112561 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94622, d112561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94622, d112561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94623 q = 1) : d112562 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94623, d112562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94623, d112562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94624 q = 1) : d112563 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94624, d112563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94624, d112563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro20854 (p : Pattern) (ha : d92315 p = 1) (hb : d94630 p = 1) : d112569 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8765 q = 1) (hb : d92315 q = 1) : d112065 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8765, d112065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20592 q ha hb
    | true =>
      simp only [d8765, d112065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20594 q ha hb
  have h2 (q : Pattern) (ha : d8766 q = 1) (hb : d92315 q = 1) : d112066 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8766, d112066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8766, d112066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94607 q = 1) : d112550 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94607, d112550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94607, d112550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94608 q = 1) : d112551 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94608, d112551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94608, d112551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94610 q = 1) : d112553 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94610, d112553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94610, d112553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20851 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94611 q = 1) : d112554 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94611, d112554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94611, d112554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94612 q = 1) : d112555 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94612, d112555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94612, d112555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92315 q = 1) (hb : d94613 q = 1) : d112556 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94613, d112556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94613, d112556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92315 q = 1) (hb : d94614 q = 1) : d112557 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94614, d112557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94614, d112557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92315 q = 1) (hb : d94625 q = 1) : d112564 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94625, d112564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94625, d112564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20853 q ha hb
  have h11 (q : Pattern) (ha : d92315 q = 1) (hb : d94626 q = 1) : d112565 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94626, d112565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94626, d112565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92315 q = 1) (hb : d94627 q = 1) : d112566 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94627, d112566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94627, d112566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92315 q = 1) (hb : d94628 q = 1) : d112567 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94628, d112567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94628, d112567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d92315 q = 1) (hb : d94629 q = 1) : d112568 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94629, d112568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94629, d112568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d92315 q = 1) (hb : d94630 q = 1) : d112569 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94630, d112569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94630, d112569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro20855 (p : Pattern) (ha : d92315 p = 1) (hb : d94636 p = 1) : d112575 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92315 q = 1) (hb : d94631 q = 1) : d112570 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94631, d112570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94631, d112570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20854 q ha hb
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94632 q = 1) : d112571 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94632, d112571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94632, d112571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94633 q = 1) : d112572 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94633, d112572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94633, d112572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94634 q = 1) : d112573 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94634, d112573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94634, d112573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94635 q = 1) : d112574 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94635, d112574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94635, d112574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94636 q = 1) : d112575 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94636, d112575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94636, d112575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20856 (p : Pattern) (ha : d92315 p = 1) (hb : d94642 p = 1) : d112581 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1633 q = 1) (hb : d92315 q = 1) : d1633 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8927 q = 1) (hb : d92315 q = 1) : d112185 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8927, d112185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20621 q ha hb
    | true =>
      simp only [d8927, d112185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8928 q = 1) (hb : d92315 q = 1) : d112186 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8928, d112186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8928, d112186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8929 q = 1) (hb : d92315 q = 1) : d112187 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8929, d112187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8929, d112187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8930 q = 1) (hb : d92315 q = 1) : d112188 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8930, d112188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8930, d112188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8931 q = 1) (hb : d92315 q = 1) : d112189 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8931, d112189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8931, d112189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94642 q = 1) : d112581 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94642, d112581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94642, d112581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro20857 (p : Pattern) (ha : d92315 p = 1) (hb : d94651 p = 1) : d112270 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9051 q = 1) (hb : d92315 q = 1) : d99062 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9051, d99062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20641 q ha hb
    | true =>
      simp only [d9051, d99062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9052 q = 1) (hb : d92315 q = 1) : d99063 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9052, d99063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9052, d99063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1909 q = 1) (hb : d92315 q = 1) : d1909 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94648 q = 1) : d112267 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d94648, d112267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94648, d112267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94649 q = 1) : d112268 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d94649, d112268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94649, d112268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94650 q = 1) : d112269 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d94650, d112269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94650, d112269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94651 q = 1) : d112270 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d94651, d112270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94651, d112270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro20858 (p : Pattern) (ha : d92315 p = 1) (hb : d94657 p = 1) : d112592 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1974 q = 1) (hb : d92315 q = 1) : d1974 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94652 q = 1) : d112587 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d94652, d112587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20857 q ha hb
    | true =>
      simp only [d94652, d112587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94653 q = 1) : d112588 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94653, d112588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94653, d112588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94654 q = 1) : d112589 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94654, d112589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94654, d112589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94655 q = 1) : d112590 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94655, d112590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94655, d112590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94656 q = 1) : d112591 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94656, d112591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94656, d112591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94657 q = 1) : d112592 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94657, d112592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94657, d112592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro20859 (p : Pattern) (ha : d92315 p = 1) (hb : d94663 p = 1) : d112598 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8933 q = 1) (hb : d92315 q = 1) : d112191 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8933, d112191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20620 q ha hb
    | true =>
      simp only [d8933, d112191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20622 q ha hb
  have h2 (q : Pattern) (ha : d8934 q = 1) (hb : d92315 q = 1) : d112192 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8934, d112192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8934, d112192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94640 q = 1) : d112579 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94640, d112579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94640, d112579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94641 q = 1) : d112580 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94641, d112580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94641, d112580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94643 q = 1) : d112582 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94643, d112582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94643, d112582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20856 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94644 q = 1) : d112583 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94644, d112583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94644, d112583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94645 q = 1) : d112584 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94645, d112584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94645, d112584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92315 q = 1) (hb : d94646 q = 1) : d112585 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94646, d112585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94646, d112585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92315 q = 1) (hb : d94647 q = 1) : d112586 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94647, d112586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94647, d112586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92315 q = 1) (hb : d94658 q = 1) : d112593 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94658, d112593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94658, d112593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20858 q ha hb
  have h11 (q : Pattern) (ha : d92315 q = 1) (hb : d94659 q = 1) : d112594 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94659, d112594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94659, d112594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92315 q = 1) (hb : d94660 q = 1) : d112595 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94660, d112595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94660, d112595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92315 q = 1) (hb : d94661 q = 1) : d112596 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94661, d112596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94661, d112596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d92315 q = 1) (hb : d94662 q = 1) : d112597 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94662, d112597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94662, d112597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d92315 q = 1) (hb : d94663 q = 1) : d112598 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94663, d112598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94663, d112598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro20860 (p : Pattern) (ha : d92315 p = 1) (hb : d94669 p = 1) : d112604 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92315 q = 1) (hb : d94664 q = 1) : d112599 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94664, d112599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94664, d112599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20859 q ha hb
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94665 q = 1) : d112600 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94665, d112600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94665, d112600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94666 q = 1) : d112601 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94666, d112601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94666, d112601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94667 q = 1) : d112602 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94667, d112602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94667, d112602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94668 q = 1) : d112603 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94668, d112603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94668, d112603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94669 q = 1) : d112604 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94669, d112604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94669, d112604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20861 (p : Pattern) (ha : d92315 p = 1) (hb : d94676 p = 1) : d112611 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2116 q = 1) (hb : d92315 q = 1) : d2116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9096 q = 1) (hb : d92315 q = 1) : d112312 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9096, d112312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20649 q ha hb
    | true =>
      simp only [d9096, d112312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9097 q = 1) (hb : d92315 q = 1) : d112313 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9097, d112313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9097, d112313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9098 q = 1) (hb : d92315 q = 1) : d112314 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9098, d112314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9098, d112314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9099 q = 1) (hb : d92315 q = 1) : d112315 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9099, d112315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9099, d112315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9100 q = 1) (hb : d92315 q = 1) : d112316 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9100, d112316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9100, d112316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94676 q = 1) : d112611 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94676, d112611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94676, d112611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro20862 (p : Pattern) (ha : d92315 p = 1) (hb : d94685 p = 1) : d112397 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9220 q = 1) (hb : d92315 q = 1) : d99125 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9220, d99125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20669 q ha hb
    | true =>
      simp only [d9220, d99125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9221 q = 1) (hb : d92315 q = 1) : d99126 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9221, d99126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9221, d99126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2387 q = 1) (hb : d92315 q = 1) : d2387 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94682 q = 1) : d112394 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d94682, d112394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94682, d112394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94683 q = 1) : d112395 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d94683, d112395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94683, d112395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94684 q = 1) : d112396 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d94684, d112396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94684, d112396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94685 q = 1) : d112397 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d94685, d112397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94685, d112397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro20863 (p : Pattern) (ha : d92315 p = 1) (hb : d94691 p = 1) : d112622 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2452 q = 1) (hb : d92315 q = 1) : d2452 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94686 q = 1) : d112617 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d94686, d112617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20862 q ha hb
    | true =>
      simp only [d94686, d112617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94687 q = 1) : d112618 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94687, d112618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94687, d112618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94688 q = 1) : d112619 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94688, d112619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94688, d112619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94689 q = 1) : d112620 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94689, d112620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94689, d112620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94690 q = 1) : d112621 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94690, d112621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94690, d112621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94691 q = 1) : d112622 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94691, d112622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94691, d112622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro20864 (p : Pattern) (ha : d92315 p = 1) (hb : d94697 p = 1) : d112628 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9102 q = 1) (hb : d92315 q = 1) : d112318 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9102, d112318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20648 q ha hb
    | true =>
      simp only [d9102, d112318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20650 q ha hb
  have h2 (q : Pattern) (ha : d9103 q = 1) (hb : d92315 q = 1) : d112319 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d9103, d112319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9103, d112319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94674 q = 1) : d112609 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94674, d112609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d94674, d112609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94675 q = 1) : d112610 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94675, d112610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94675, d112610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94677 q = 1) : d112612 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94677, d112612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94677, d112612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20861 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94678 q = 1) : d112613 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94678, d112613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94678, d112613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94679 q = 1) : d112614 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94679, d112614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94679, d112614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d92315 q = 1) (hb : d94680 q = 1) : d112615 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94680, d112615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94680, d112615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d92315 q = 1) (hb : d94681 q = 1) : d112616 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94681, d112616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94681, d112616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92315 q = 1) (hb : d94692 q = 1) : d112623 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94692, d112623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94692, d112623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20863 q ha hb
  have h11 (q : Pattern) (ha : d92315 q = 1) (hb : d94693 q = 1) : d112624 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94693, d112624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94693, d112624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d92315 q = 1) (hb : d94694 q = 1) : d112625 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94694, d112625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94694, d112625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d92315 q = 1) (hb : d94695 q = 1) : d112626 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94695, d112626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94695, d112626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d92315 q = 1) (hb : d94696 q = 1) : d112627 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94696, d112627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94696, d112627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d92315 q = 1) (hb : d94697 q = 1) : d112628 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94697, d112628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94697, d112628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro20865 (p : Pattern) (ha : d92315 p = 1) (hb : d94703 p = 1) : d112634 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92315 q = 1) (hb : d94698 q = 1) : d112629 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94698, d112629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94698, d112629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20864 q ha hb
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94699 q = 1) : d112630 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94699, d112630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94699, d112630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94700 q = 1) : d112631 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94700, d112631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94700, d112631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94701 q = 1) : d112632 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94701, d112632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94701, d112632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94702 q = 1) : d112633 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94702, d112633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94702, d112633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94703 q = 1) : d112634 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94703, d112634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d94703, d112634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20866 (p : Pattern) (ha : d92315 p = 1) (hb : d94709 p = 1) : d112640 p = 1 := by
  have h0 (q : Pattern) (ha : d92315 q = 1) (hb : d94574 q = 1) : d112521 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94574, d112521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20840 q ha hb
    | true =>
      simp only [d94574, d112521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20845 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94605 q = 1) : d112548 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94605, d112548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94605, d112548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20850 q ha hb
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94606 q = 1) : d112549 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94606, d112549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94606, d112549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94637 q = 1) : d112576 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94637, d112576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94637, d112576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20855 q ha hb
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94638 q = 1) : d112577 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94638, d112577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94638, d112577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94639 q = 1) : d112578 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94639, d112578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94639, d112578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d92315 q = 1) (hb : d94670 q = 1) : d112605 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94670, d112605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94670, d112605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20860 q ha hb
  have h8 (q : Pattern) (ha : d92315 q = 1) (hb : d94671 q = 1) : d112606 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94671, d112606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94671, d112606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d92315 q = 1) (hb : d94672 q = 1) : d112607 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94672, d112607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94672, d112607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d92315 q = 1) (hb : d94673 q = 1) : d112608 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d94673, d112608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94673, d112608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d92315 q = 1) (hb : d94704 q = 1) : d112635 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d94704, d112635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94704, d112635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20865 q ha hb
  have h12 (q : Pattern) (ha : d92315 q = 1) (hb : d94705 q = 1) : d112636 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d94705, d112636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94705, d112636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d92315 q = 1) (hb : d94706 q = 1) : d112637 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d94706, d112637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94706, d112637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d92315 q = 1) (hb : d94707 q = 1) : d112638 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d94707, d112638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d94707, d112638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d92315 q = 1) (hb : d94708 q = 1) : d112639 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d94708, d112639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94708, d112639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d92315 q = 1) (hb : d94709 q = 1) : d112640 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d94709, d112640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94709, d112640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro20867 (p : Pattern) (ha : d92315 p = 1) (hb : d94715 p = 1) : d112646 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92315 q = 1) (hb : d94710 q = 1) : d112641 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d94710, d112641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20866 q ha hb
    | true =>
      simp only [d94710, d112641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94711 q = 1) : d112642 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d94711, d112642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94711, d112642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94712 q = 1) : d112643 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d94712, d112643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94712, d112643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94713 q = 1) : d112644 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d94713, d112644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94713, d112644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94714 q = 1) : d112645 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d94714, d112645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94714, d112645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94715 q = 1) : d112646 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d94715, d112646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94715, d112646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20868 (p : Pattern) (ha : d92315 p = 1) (hb : d94721 p = 1) : d112652 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92315 q = 1) (hb : d94716 q = 1) : d112647 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d94716, d112647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20867 q ha hb
    | true =>
      simp only [d94716, d112647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94717 q = 1) : d112648 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d94717, d112648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94717, d112648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94718 q = 1) : d112649 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d94718, d112649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94718, d112649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94719 q = 1) : d112650 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d94719, d112650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94719, d112650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94720 q = 1) : d112651 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d94720, d112651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94720, d112651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94721 q = 1) : d112652 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d94721, d112652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94721, d112652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20869 (p : Pattern) (ha : d92315 p = 1) (hb : d94727 p = 1) : d112658 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92315 q = 1) (hb : d94722 q = 1) : d112653 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d94722, d112653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20868 q ha hb
    | true =>
      simp only [d94722, d112653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94723 q = 1) : d112654 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d94723, d112654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94723, d112654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94724 q = 1) : d112655 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d94724, d112655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94724, d112655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94725 q = 1) : d112656 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d94725, d112656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94725, d112656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94726 q = 1) : d112657 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d94726, d112657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94726, d112657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94727 q = 1) : d112658 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d94727, d112658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94727, d112658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20870 (p : Pattern) (ha : d92315 p = 1) (hb : d94733 p = 1) : d112664 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92315 q = 1) (hb : d94728 q = 1) : d112659 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d94728, d112659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20869 q ha hb
    | true =>
      simp only [d94728, d112659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94729 q = 1) : d112660 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d94729, d112660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94729, d112660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94730 q = 1) : d112661 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d94730, d112661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94730, d112661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94731 q = 1) : d112662 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d94731, d112662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94731, d112662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94732 q = 1) : d112663 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d94732, d112663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94732, d112663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94733 q = 1) : d112664 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d94733, d112664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94733, d112664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20871 (p : Pattern) (ha : d92315 p = 1) (hb : d94739 p = 1) : d112670 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92315 q = 1) (hb : d94734 q = 1) : d112665 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d94734, d112665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20870 q ha hb
    | true =>
      simp only [d94734, d112665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94735 q = 1) : d112666 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d94735, d112666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94735, d112666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94736 q = 1) : d112667 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d94736, d112667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94736, d112667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94737 q = 1) : d112668 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d94737, d112668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94737, d112668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94738 q = 1) : d112669 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d94738, d112669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94738, d112669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94739 q = 1) : d112670 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d94739, d112670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94739, d112670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20872 (p : Pattern) (ha : d92315 p = 1) (hb : d94745 p = 1) : d112676 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92315 q = 1) (hb : d94740 q = 1) : d112671 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d94740, d112671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20871 q ha hb
    | true =>
      simp only [d94740, d112671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94741 q = 1) : d112672 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d94741, d112672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94741, d112672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94742 q = 1) : d112673 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d94742, d112673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94742, d112673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94743 q = 1) : d112674 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d94743, d112674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94743, d112674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94744 q = 1) : d112675 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d94744, d112675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94744, d112675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94745 q = 1) : d112676 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d94745, d112676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94745, d112676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20873 (p : Pattern) (ha : d92315 p = 1) (hb : d94751 p = 1) : d112682 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d92315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d92315 q = 1) (hb : d94746 q = 1) : d112677 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d94746, d112677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20872 q ha hb
    | true =>
      simp only [d94746, d112677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d92315 q = 1) (hb : d94747 q = 1) : d112678 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d94747, d112678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94747, d112678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d92315 q = 1) (hb : d94748 q = 1) : d112679 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d94748, d112679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94748, d112679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d92315 q = 1) (hb : d94749 q = 1) : d112680 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d94749, d112680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d94749, d112680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d92315 q = 1) (hb : d94750 q = 1) : d112681 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d94750, d112681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94750, d112681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d92315 q = 1) (hb : d94751 q = 1) : d112682 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d94751, d112682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94751, d112682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20874 (p : Pattern) (ha : d83767 p = 1) (hb : d111718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83741 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83747 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d83756 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d83671 q = 1) (hb : d111668 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83671, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20682 q ha hb
    | true =>
      simp only [d83671, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d83757 q = 1) (hb : d111714 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83757, d111714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d83757, d111714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d83763 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d83764 q = 1) (hb : d111715 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83764, d111715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83764, d111715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d83765 q = 1) (hb : d111716 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83765, d111716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d83765, d111716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83766 q = 1) (hb : d111717 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83766, d111717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83766, d111717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83767 q = 1) (hb : d111718 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83767, d111718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83767, d111718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro20875 (p : Pattern) (ha : d83786 p = 1) (hb : d111725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83741 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83747 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83756 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83671 q = 1) (hb : d111668 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83671, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20682 q ha hb
    | true =>
      simp only [d83671, d111668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d83757 q = 1) (hb : d111714 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83757, d111714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d83757, d111714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83763 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d83764 q = 1) (hb : d111715 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83764, d111715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83764, d111715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d83765 q = 1) (hb : d111716 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83765, d111716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83765, d111716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83766 q = 1) (hb : d111717 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83766, d111717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83766, d111717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d83772 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d83776 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d83778 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d83678 q = 1) (hb : d111675 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83678, d111675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20684 q ha hb
    | true =>
      simp only [d83678, d111675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d83779 q = 1) (hb : d111721 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83779, d111721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d83779, d111721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d83782 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d83783 q = 1) (hb : d111722 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83783, d111722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d83783, d111722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d83784 q = 1) (hb : d111723 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83784, d111723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d83784, d111723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d83785 q = 1) (hb : d111724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83785, d111724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d83785, d111724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d83786 q = 1) (hb : d111725 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83786, d111725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83786, d111725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro20876 (p : Pattern) (ha : d83795 p = 1) (hb : d112472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83778 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d83678 q = 1) (hb : d111675 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83678, d111675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20684 q ha hb
    | true =>
      simp only [d83678, d111675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d83779 q = 1) (hb : d111721 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83779, d111721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83779, d111721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d83782 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d83783 q = 1) (hb : d111722 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83783, d111722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83783, d111722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83793 q = 1) (hb : d111723 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83793, d111723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83793, d111723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83794 q = 1) (hb : d111724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83794, d111724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83794, d111724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83795 q = 1) (hb : d112472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83795, d112472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83795, d112472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20877 (p : Pattern) (ha : d83820 p = 1) (hb : d112482 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83809 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d83704 q = 1) (hb : d111697 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83704, d111697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20687 q ha hb
    | true =>
      simp only [d83704, d111697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d83810 q = 1) (hb : d112478 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83810, d112478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83810, d112478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d83816 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d83817 q = 1) (hb : d112479 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83817, d112479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83817, d112479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83818 q = 1) (hb : d112480 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83818, d112480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83818, d112480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83819 q = 1) (hb : d112481 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83819, d112481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83819, d112481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83820 q = 1) (hb : d112482 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83820, d112482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83820, d112482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20878 (p : Pattern) (ha : d83826 p = 1) (hb : d112488 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83787 q = 1) (hb : d111726 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83787, d111726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20874 q ha hb
    | true =>
      simp only [d83787, d111726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20875 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83789 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83790 q = 1) (hb : d111727 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83790, d111727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83790, d111727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d83791 q = 1) (hb : d112470 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83791, d112470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83791, d112470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83792 q = 1) (hb : d112471 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83792, d112471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83792, d112471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83796 q = 1) (hb : d112473 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83796, d112473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d83796, d112473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20876 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d83797 q = 1) (hb : d112474 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83797, d112474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83797, d112474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d83798 q = 1) (hb : d112475 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83798, d112475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d83798, d112475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d83799 q = 1) (hb : d112476 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83799, d112476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83799, d112476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d83800 q = 1) (hb : d112477 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83800, d112477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83800, d112477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d83821 q = 1) (hb : d112483 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83821, d112483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d83821, d112483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20877 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d83822 q = 1) (hb : d112484 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83822, d112484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d83822, d112484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d83823 q = 1) (hb : d112485 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83823, d112485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d83823, d112485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d83824 q = 1) (hb : d112486 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83824, d112486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d83824, d112486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d83825 q = 1) (hb : d112487 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83825, d112487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d83825, d112487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d83826 q = 1) (hb : d112488 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d83826, d112488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d83826, d112488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro20879 (p : Pattern) (ha : d83832 p = 1) (hb : d112494 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d83716 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d83716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d83716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10167 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d83717 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d83717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d83717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d83718 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d83718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d83718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d83719 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d83719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d83719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d83720 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d83720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d83720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83827 q = 1) (hb : d112489 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d83827, d112489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83827, d112489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20878 q ha hb
  have h8 (q : Pattern) (ha : d83828 q = 1) (hb : d112490 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d83828, d112490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83828, d112490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83829 q = 1) (hb : d112491 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d83829, d112491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83829, d112491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83830 q = 1) (hb : d112492 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d83830, d112492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83830, d112492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d83831 q = 1) (hb : d112493 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d83831, d112493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83831, d112493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d83832 q = 1) (hb : d112494 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d83832, d112494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d83832, d112494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro20880 (p : Pattern) (ha : d83886 p = 1) (hb : d111811 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83860 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83866 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d83875 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d83837 q = 1) (hb : d111806 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83837, d111806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20709 q ha hb
    | true =>
      simp only [d83837, d111806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q hb ha
  have h5 (q : Pattern) (ha : d83876 q = 1) (hb : d111807 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83876, d111807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d83876, d111807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d83882 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d83883 q = 1) (hb : d111808 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83883, d111808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d83883, d111808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d83884 q = 1) (hb : d111809 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83884, d111809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d83884, d111809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83885 q = 1) (hb : d111810 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83885, d111810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83885, d111810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83886 q = 1) (hb : d111811 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83886, d111811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83886, d111811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro20881 (p : Pattern) (ha : d83905 p = 1) (hb : d111819 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83860 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83866 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83875 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83837 q = 1) (hb : d111806 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83837, d111806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20709 q ha hb
    | true =>
      simp only [d83837, d111806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro63 q hb ha
  have h4 (q : Pattern) (ha : d83876 q = 1) (hb : d111807 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83876, d111807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d83876, d111807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d83882 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d83883 q = 1) (hb : d111808 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83883, d111808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d83883, d111808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d83884 q = 1) (hb : d111809 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83884, d111809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83884, d111809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83885 q = 1) (hb : d111810 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83885, d111810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83885, d111810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d83891 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d83895 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d83897 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d83846 q = 1) (hb : d111814 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83846, d111814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20711 q ha hb
    | true =>
      simp only [d83846, d111814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66 q hb ha
  have h13 (q : Pattern) (ha : d83898 q = 1) (hb : d111815 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83898, d111815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d83898, d111815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d83901 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d83902 q = 1) (hb : d111816 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83902, d111816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d83902, d111816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d83903 q = 1) (hb : d111817 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83903, d111817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d83903, d111817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d83904 q = 1) (hb : d111818 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83904, d111818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d83904, d111818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d83905 q = 1) (hb : d111819 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83905, d111819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d83905, d111819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro20882 (p : Pattern) (ha : d83914 p = 1) (hb : d112497 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83897 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d83846 q = 1) (hb : d111814 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83846, d111814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20711 q ha hb
    | true =>
      simp only [d83846, d111814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro66 q hb ha
  have h3 (q : Pattern) (ha : d83898 q = 1) (hb : d111815 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83898, d111815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83898, d111815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d83901 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d83902 q = 1) (hb : d111816 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83902, d111816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83902, d111816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83912 q = 1) (hb : d111817 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83912, d111817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83912, d111817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83913 q = 1) (hb : d111818 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83913, d111818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83913, d111818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83914 q = 1) (hb : d112497 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83914, d112497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83914, d112497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20883 (p : Pattern) (ha : d83944 p = 1) (hb : d112508 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83932 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d83933 q = 1) (hb : d112503 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83933, d112503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20728 q ha hb
    | true =>
      simp only [d83933, d112503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro72 q hb ha
  have h3 (q : Pattern) (ha : d83934 q = 1) (hb : d112504 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d83934, d112504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d83934, d112504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d83940 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d83941 q = 1) (hb : d112505 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d83941, d112505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83941, d112505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83942 q = 1) (hb : d112506 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d83942, d112506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83942, d112506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83943 q = 1) (hb : d112507 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d83943, d112507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83943, d112507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83944 q = 1) (hb : d112508 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d83944, d112508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83944, d112508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20884 (p : Pattern) (ha : d83950 p = 1) (hb : d112514 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83854 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83906 q = 1) (hb : d111820 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83906, d111820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20880 q ha hb
    | true =>
      simp only [d83906, d111820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20881 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83908 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83909 q = 1) (hb : d111821 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83909, d111821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d83909, d111821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d83910 q = 1) (hb : d112495 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83910, d112495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d83910, d112495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83911 q = 1) (hb : d112496 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83911, d112496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83911, d112496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83915 q = 1) (hb : d112498 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83915, d112498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d83915, d112498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20882 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52358 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d83916 q = 1) (hb : d112499 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83916, d112499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d83916, d112499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d83917 q = 1) (hb : d112500 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83917, d112500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d83917, d112500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d83918 q = 1) (hb : d112501 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83918, d112501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d83918, d112501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d83919 q = 1) (hb : d112502 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83919, d112502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d83919, d112502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d83945 q = 1) (hb : d112509 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d83945, d112509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d83945, d112509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20883 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52414 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d83946 q = 1) (hb : d112510 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d83946, d112510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d83946, d112510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d83947 q = 1) (hb : d112511 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d83947, d112511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d83947, d112511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d83948 q = 1) (hb : d112512 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d83948, d112512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d83948, d112512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d83949 q = 1) (hb : d112513 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d83949, d112513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d83949, d112513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d83950 q = 1) (hb : d112514 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d83950, d112514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d83950, d112514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro20885 (p : Pattern) (ha : d83956 p = 1) (hb : d112520 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83951 q = 1) (hb : d112515 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d83951, d112515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83951, d112515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20884 q ha hb
  have h2 (q : Pattern) (ha : d83952 q = 1) (hb : d112516 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d83952, d112516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83952, d112516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83953 q = 1) (hb : d112517 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d83953, d112517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83953, d112517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d83954 q = 1) (hb : d112518 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d83954, d112518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83954, d112518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83955 q = 1) (hb : d112519 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d83955, d112519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83955, d112519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83956 q = 1) (hb : d112520 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d83956, d112520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d83956, d112520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20886 (p : Pattern) (ha : d84015 p = 1) (hb : d111930 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83989 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83995 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d84004 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d83966 q = 1) (hb : d111925 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83966, d111925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20733 q ha hb
    | true =>
      simp only [d83966, d111925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q hb ha
  have h5 (q : Pattern) (ha : d84005 q = 1) (hb : d111926 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84005, d111926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d84005, d111926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d84011 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d84012 q = 1) (hb : d111927 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84012, d111927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84012, d111927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d84013 q = 1) (hb : d111928 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84013, d111928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d84013, d111928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84014 q = 1) (hb : d111929 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84014, d111929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84014, d111929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84015 q = 1) (hb : d111930 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84015, d111930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84015, d111930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro20887 (p : Pattern) (ha : d84034 p = 1) (hb : d111939 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83989 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83995 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84004 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83966 q = 1) (hb : d111925 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83966, d111925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20733 q ha hb
    | true =>
      simp only [d83966, d111925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro107 q hb ha
  have h4 (q : Pattern) (ha : d84005 q = 1) (hb : d111926 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84005, d111926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d84005, d111926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d84011 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d84012 q = 1) (hb : d111927 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84012, d111927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84012, d111927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d84013 q = 1) (hb : d111928 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84013, d111928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84013, d111928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84014 q = 1) (hb : d111929 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84014, d111929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84014, d111929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d84020 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d84024 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d84026 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d83975 q = 1) (hb : d111934 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83975, d111934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20735 q ha hb
    | true =>
      simp only [d83975, d111934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro110 q hb ha
  have h13 (q : Pattern) (ha : d84027 q = 1) (hb : d111935 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84027, d111935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d84027, d111935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d84030 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d84031 q = 1) (hb : d111936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84031, d111936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84031, d111936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d84032 q = 1) (hb : d111937 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84032, d111937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d84032, d111937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d84033 q = 1) (hb : d111938 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84033, d111938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d84033, d111938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d84034 q = 1) (hb : d111939 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84034, d111939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84034, d111939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro20888 (p : Pattern) (ha : d84043 p = 1) (hb : d112524 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84026 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d83975 q = 1) (hb : d111934 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d83975, d111934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20735 q ha hb
    | true =>
      simp only [d83975, d111934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro110 q hb ha
  have h3 (q : Pattern) (ha : d84027 q = 1) (hb : d111935 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84027, d111935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84027, d111935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d84030 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84031 q = 1) (hb : d111936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84031, d111936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84031, d111936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84041 q = 1) (hb : d111937 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84041, d111937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84041, d111937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84042 q = 1) (hb : d111938 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84042, d111938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84042, d111938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84043 q = 1) (hb : d112524 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84043, d112524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84043, d112524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20889 (p : Pattern) (ha : d84077 p = 1) (hb : d112535 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84065 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84066 q = 1) (hb : d112530 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84066, d112530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20752 q ha hb
    | true =>
      simp only [d84066, d112530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro118 q hb ha
  have h3 (q : Pattern) (ha : d84067 q = 1) (hb : d112531 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84067, d112531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84067, d112531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d84073 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84074 q = 1) (hb : d112532 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84074, d112532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84074, d112532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84075 q = 1) (hb : d112533 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84075, d112533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84075, d112533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84076 q = 1) (hb : d112534 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84076, d112534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84076, d112534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84077 q = 1) (hb : d112535 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84077, d112535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84077, d112535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20890 (p : Pattern) (ha : d84083 p = 1) (hb : d112541 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83983 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84035 q = 1) (hb : d111940 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84035, d111940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20886 q ha hb
    | true =>
      simp only [d84035, d111940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20887 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84037 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84038 q = 1) (hb : d111941 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84038, d111941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84038, d111941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84039 q = 1) (hb : d112522 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84039, d112522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84039, d112522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84040 q = 1) (hb : d112523 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84040, d112523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84040, d112523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84044 q = 1) (hb : d112525 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84044, d112525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d84044, d112525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20888 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52579 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d84045 q = 1) (hb : d112526 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84045, d112526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84045, d112526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d84046 q = 1) (hb : d112527 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84046, d112527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d84046, d112527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d84047 q = 1) (hb : d112528 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84047, d112528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84047, d112528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d84048 q = 1) (hb : d112529 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84048, d112529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84048, d112529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d84078 q = 1) (hb : d112536 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84078, d112536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d84078, d112536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20889 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52651 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d84079 q = 1) (hb : d112537 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84079, d112537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84079, d112537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d84080 q = 1) (hb : d112538 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84080, d112538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d84080, d112538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d84081 q = 1) (hb : d112539 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84081, d112539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d84081, d112539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d84082 q = 1) (hb : d112540 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84082, d112540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84082, d112540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d84083 q = 1) (hb : d112541 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d84083, d112541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d84083, d112541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro20891 (p : Pattern) (ha : d84089 p = 1) (hb : d112547 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84084 q = 1) (hb : d112542 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d84084, d112542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84084, d112542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20890 q ha hb
  have h2 (q : Pattern) (ha : d84085 q = 1) (hb : d112543 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d84085, d112543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84085, d112543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84086 q = 1) (hb : d112544 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d84086, d112544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84086, d112544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d84087 q = 1) (hb : d112545 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d84087, d112545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84087, d112545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84088 q = 1) (hb : d112546 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d84088, d112546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84088, d112546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84089 q = 1) (hb : d112547 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d84089, d112547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84089, d112547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20892 (p : Pattern) (ha : d84149 p = 1) (hb : d112055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84123 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84129 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d84138 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d84100 q = 1) (hb : d112050 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84100, d112050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20757 q ha hb
    | true =>
      simp only [d84100, d112050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q hb ha
  have h5 (q : Pattern) (ha : d84139 q = 1) (hb : d112051 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84139, d112051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d84139, d112051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d84145 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d84146 q = 1) (hb : d112052 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84146, d112052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84146, d112052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d84147 q = 1) (hb : d112053 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84147, d112053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d84147, d112053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84148 q = 1) (hb : d112054 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84148, d112054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84148, d112054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84149 q = 1) (hb : d112055 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84149, d112055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84149, d112055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro20893 (p : Pattern) (ha : d84168 p = 1) (hb : d112064 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d84123 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84129 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84138 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84100 q = 1) (hb : d112050 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84100, d112050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20757 q ha hb
    | true =>
      simp only [d84100, d112050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro159 q hb ha
  have h4 (q : Pattern) (ha : d84139 q = 1) (hb : d112051 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84139, d112051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d84139, d112051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d84145 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d84146 q = 1) (hb : d112052 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84146, d112052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84146, d112052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d84147 q = 1) (hb : d112053 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84147, d112053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84147, d112053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84148 q = 1) (hb : d112054 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84148, d112054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84148, d112054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d84154 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d84158 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d84160 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d84109 q = 1) (hb : d112059 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84109, d112059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20759 q ha hb
    | true =>
      simp only [d84109, d112059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro162 q hb ha
  have h13 (q : Pattern) (ha : d84161 q = 1) (hb : d112060 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84161, d112060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d84161, d112060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d84164 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d84165 q = 1) (hb : d112061 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84165, d112061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84165, d112061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d84166 q = 1) (hb : d112062 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84166, d112062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d84166, d112062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d84167 q = 1) (hb : d112063 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84167, d112063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d84167, d112063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d84168 q = 1) (hb : d112064 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84168, d112064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84168, d112064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro20894 (p : Pattern) (ha : d84177 p = 1) (hb : d112552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84160 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84109 q = 1) (hb : d112059 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84109, d112059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20759 q ha hb
    | true =>
      simp only [d84109, d112059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro162 q hb ha
  have h3 (q : Pattern) (ha : d84161 q = 1) (hb : d112060 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84161, d112060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84161, d112060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d84164 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84165 q = 1) (hb : d112061 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84165, d112061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84165, d112061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84175 q = 1) (hb : d112062 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84175, d112062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84175, d112062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84176 q = 1) (hb : d112063 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84176, d112063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84176, d112063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84177 q = 1) (hb : d112552 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84177, d112552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84177, d112552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20895 (p : Pattern) (ha : d84211 p = 1) (hb : d112563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84199 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84200 q = 1) (hb : d112558 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84200, d112558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20776 q ha hb
    | true =>
      simp only [d84200, d112558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro170 q hb ha
  have h3 (q : Pattern) (ha : d84201 q = 1) (hb : d112559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84201, d112559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84201, d112559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d84207 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84208 q = 1) (hb : d112560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84208, d112560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84208, d112560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84209 q = 1) (hb : d112561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84209, d112561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84209, d112561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84210 q = 1) (hb : d112562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84210, d112562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84210, d112562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84211 q = 1) (hb : d112563 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84211, d112563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84211, d112563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20896 (p : Pattern) (ha : d84217 p = 1) (hb : d112569 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d84117 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84169 q = 1) (hb : d112065 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84169, d112065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20892 q ha hb
    | true =>
      simp only [d84169, d112065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20893 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84171 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84172 q = 1) (hb : d112066 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84172, d112066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84172, d112066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84173 q = 1) (hb : d112550 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84173, d112550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84173, d112550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84174 q = 1) (hb : d112551 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84174, d112551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84174, d112551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84178 q = 1) (hb : d112553 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84178, d112553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d84178, d112553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20894 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52859 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d84179 q = 1) (hb : d112554 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84179, d112554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84179, d112554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d84180 q = 1) (hb : d112555 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84180, d112555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d84180, d112555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d84181 q = 1) (hb : d112556 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84181, d112556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84181, d112556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d84182 q = 1) (hb : d112557 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84182, d112557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84182, d112557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d84212 q = 1) (hb : d112564 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84212, d112564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d84212, d112564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20895 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52945 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d84213 q = 1) (hb : d112565 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84213, d112565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84213, d112565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d84214 q = 1) (hb : d112566 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84214, d112566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d84214, d112566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d84215 q = 1) (hb : d112567 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84215, d112567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d84215, d112567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d84216 q = 1) (hb : d112568 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84216, d112568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84216, d112568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d84217 q = 1) (hb : d112569 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d84217, d112569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d84217, d112569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro20897 (p : Pattern) (ha : d84223 p = 1) (hb : d112575 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84218 q = 1) (hb : d112570 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d84218, d112570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84218, d112570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20896 q ha hb
  have h2 (q : Pattern) (ha : d84219 q = 1) (hb : d112571 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d84219, d112571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84219, d112571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84220 q = 1) (hb : d112572 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d84220, d112572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84220, d112572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d84221 q = 1) (hb : d112573 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d84221, d112573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84221, d112573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84222 q = 1) (hb : d112574 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d84222, d112574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84222, d112574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84223 q = 1) (hb : d112575 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d84223, d112575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84223, d112575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20898 (p : Pattern) (ha : d84284 p = 1) (hb : d112181 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84258 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84264 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d84273 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d84235 q = 1) (hb : d112176 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84235, d112176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20781 q ha hb
    | true =>
      simp only [d84235, d112176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q hb ha
  have h5 (q : Pattern) (ha : d84274 q = 1) (hb : d112177 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84274, d112177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d84274, d112177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d84280 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d84281 q = 1) (hb : d112178 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84281, d112178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84281, d112178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d84282 q = 1) (hb : d112179 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84282, d112179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d84282, d112179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84283 q = 1) (hb : d112180 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84283, d112180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84283, d112180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84284 q = 1) (hb : d112181 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84284, d112181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84284, d112181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro20899 (p : Pattern) (ha : d84303 p = 1) (hb : d112190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d84258 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84264 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84273 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84235 q = 1) (hb : d112176 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84235, d112176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20781 q ha hb
    | true =>
      simp only [d84235, d112176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro217 q hb ha
  have h4 (q : Pattern) (ha : d84274 q = 1) (hb : d112177 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84274, d112177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d84274, d112177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d84280 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d84281 q = 1) (hb : d112178 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84281, d112178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84281, d112178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d84282 q = 1) (hb : d112179 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84282, d112179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84282, d112179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84283 q = 1) (hb : d112180 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84283, d112180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84283, d112180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d84289 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d84293 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d84295 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d84244 q = 1) (hb : d112185 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84244, d112185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20783 q ha hb
    | true =>
      simp only [d84244, d112185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro220 q hb ha
  have h13 (q : Pattern) (ha : d84296 q = 1) (hb : d112186 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84296, d112186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d84296, d112186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d84299 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d84300 q = 1) (hb : d112187 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84300, d112187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84300, d112187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d84301 q = 1) (hb : d112188 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84301, d112188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d84301, d112188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d84302 q = 1) (hb : d112189 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84302, d112189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d84302, d112189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d84303 q = 1) (hb : d112190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84303, d112190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84303, d112190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro20900 (p : Pattern) (ha : d84312 p = 1) (hb : d112581 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84295 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84244 q = 1) (hb : d112185 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84244, d112185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20783 q ha hb
    | true =>
      simp only [d84244, d112185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro220 q hb ha
  have h3 (q : Pattern) (ha : d84296 q = 1) (hb : d112186 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84296, d112186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84296, d112186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d84299 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84300 q = 1) (hb : d112187 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84300, d112187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84300, d112187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84310 q = 1) (hb : d112188 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84310, d112188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84310, d112188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84311 q = 1) (hb : d112189 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84311, d112189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84311, d112189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84312 q = 1) (hb : d112581 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84312, d112581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84312, d112581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20901 (p : Pattern) (ha : d84346 p = 1) (hb : d112592 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84334 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84335 q = 1) (hb : d112587 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84335, d112587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20800 q ha hb
    | true =>
      simp only [d84335, d112587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro228 q hb ha
  have h3 (q : Pattern) (ha : d84336 q = 1) (hb : d112588 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84336, d112588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84336, d112588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d84342 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84343 q = 1) (hb : d112589 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84343, d112589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84343, d112589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84344 q = 1) (hb : d112590 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84344, d112590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84344, d112590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84345 q = 1) (hb : d112591 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84345, d112591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84345, d112591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84346 q = 1) (hb : d112592 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84346, d112592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84346, d112592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20902 (p : Pattern) (ha : d84352 p = 1) (hb : d112598 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d84252 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84304 q = 1) (hb : d112191 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84304, d112191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20898 q ha hb
    | true =>
      simp only [d84304, d112191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20899 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84306 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84307 q = 1) (hb : d112192 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84307, d112192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84307, d112192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84308 q = 1) (hb : d112579 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84308, d112579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84308, d112579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84309 q = 1) (hb : d112580 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84309, d112580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84309, d112580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84313 q = 1) (hb : d112582 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84313, d112582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d84313, d112582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20900 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53174 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d84314 q = 1) (hb : d112583 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84314, d112583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84314, d112583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d84315 q = 1) (hb : d112584 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84315, d112584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d84315, d112584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d84316 q = 1) (hb : d112585 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84316, d112585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84316, d112585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d84317 q = 1) (hb : d112586 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84317, d112586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84317, d112586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d84347 q = 1) (hb : d112593 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84347, d112593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d84347, d112593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20901 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53260 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d84348 q = 1) (hb : d112594 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84348, d112594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84348, d112594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d84349 q = 1) (hb : d112595 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84349, d112595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d84349, d112595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d84350 q = 1) (hb : d112596 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84350, d112596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d84350, d112596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d84351 q = 1) (hb : d112597 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84351, d112597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84351, d112597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d84352 q = 1) (hb : d112598 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d84352, d112598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d84352, d112598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro20903 (p : Pattern) (ha : d84358 p = 1) (hb : d112604 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84353 q = 1) (hb : d112599 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d84353, d112599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84353, d112599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20902 q ha hb
  have h2 (q : Pattern) (ha : d84354 q = 1) (hb : d112600 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d84354, d112600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84354, d112600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84355 q = 1) (hb : d112601 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d84355, d112601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84355, d112601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d84356 q = 1) (hb : d112602 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d84356, d112602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84356, d112602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84357 q = 1) (hb : d112603 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d84357, d112603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84357, d112603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84358 q = 1) (hb : d112604 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d84358, d112604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84358, d112604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20904 (p : Pattern) (ha : d84420 p = 1) (hb : d112308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84394 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84400 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d84409 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d84371 q = 1) (hb : d112303 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84371, d112303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20805 q ha hb
    | true =>
      simp only [d84371, d112303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q hb ha
  have h5 (q : Pattern) (ha : d84410 q = 1) (hb : d112304 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84410, d112304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d84410, d112304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d84416 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d84417 q = 1) (hb : d112305 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84417, d112305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84417, d112305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d84418 q = 1) (hb : d112306 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84418, d112306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d84418, d112306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84419 q = 1) (hb : d112307 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84419, d112307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84419, d112307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84420 q = 1) (hb : d112308 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84420, d112308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84420, d112308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro20905 (p : Pattern) (ha : d84439 p = 1) (hb : d112317 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d84394 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84400 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84409 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84371 q = 1) (hb : d112303 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84371, d112303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20805 q ha hb
    | true =>
      simp only [d84371, d112303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro276 q hb ha
  have h4 (q : Pattern) (ha : d84410 q = 1) (hb : d112304 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84410, d112304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d84410, d112304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d84416 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d84417 q = 1) (hb : d112305 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84417, d112305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84417, d112305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d84418 q = 1) (hb : d112306 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84418, d112306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84418, d112306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84419 q = 1) (hb : d112307 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84419, d112307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84419, d112307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d84425 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d84429 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d84431 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d84380 q = 1) (hb : d112312 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84380, d112312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20807 q ha hb
    | true =>
      simp only [d84380, d112312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro279 q hb ha
  have h13 (q : Pattern) (ha : d84432 q = 1) (hb : d112313 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84432, d112313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d84432, d112313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d84435 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d84436 q = 1) (hb : d112314 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84436, d112314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84436, d112314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d84437 q = 1) (hb : d112315 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84437, d112315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d84437, d112315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d84438 q = 1) (hb : d112316 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84438, d112316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d84438, d112316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d84439 q = 1) (hb : d112317 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84439, d112317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d84439, d112317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro20906 (p : Pattern) (ha : d84448 p = 1) (hb : d112611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84431 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84380 q = 1) (hb : d112312 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84380, d112312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20807 q ha hb
    | true =>
      simp only [d84380, d112312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro279 q hb ha
  have h3 (q : Pattern) (ha : d84432 q = 1) (hb : d112313 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84432, d112313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84432, d112313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d84435 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84436 q = 1) (hb : d112314 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84436, d112314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84436, d112314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84446 q = 1) (hb : d112315 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84446, d112315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84446, d112315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84447 q = 1) (hb : d112316 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84447, d112316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84447, d112316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84448 q = 1) (hb : d112611 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84448, d112611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84448, d112611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20907 (p : Pattern) (ha : d84482 p = 1) (hb : d112622 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d84470 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84471 q = 1) (hb : d112617 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84471, d112617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20824 q ha hb
    | true =>
      simp only [d84471, d112617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro287 q hb ha
  have h3 (q : Pattern) (ha : d84472 q = 1) (hb : d112618 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d84472, d112618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84472, d112618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d84478 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84479 q = 1) (hb : d112619 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d84479, d112619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84479, d112619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84480 q = 1) (hb : d112620 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d84480, d112620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84480, d112620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84481 q = 1) (hb : d112621 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d84481, d112621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84481, d112621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d84482 q = 1) (hb : d112622 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d84482, d112622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84482, d112622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20908 (p : Pattern) (ha : d84488 p = 1) (hb : d112628 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d84388 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84440 q = 1) (hb : d112318 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84440, d112318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20904 q ha hb
    | true =>
      simp only [d84440, d112318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20905 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84442 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d84443 q = 1) (hb : d112319 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84443, d112319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84443, d112319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84444 q = 1) (hb : d112609 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84444, d112609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84444, d112609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d84445 q = 1) (hb : d112610 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84445, d112610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84445, d112610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84449 q = 1) (hb : d112612 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84449, d112612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d84449, d112612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20906 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53491 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d84450 q = 1) (hb : d112613 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84450, d112613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d84450, d112613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d84451 q = 1) (hb : d112614 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84451, d112614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d84451, d112614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d84452 q = 1) (hb : d112615 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84452, d112615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84452, d112615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d84453 q = 1) (hb : d112616 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84453, d112616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84453, d112616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d84483 q = 1) (hb : d112623 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d84483, d112623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d84483, d112623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20907 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d53577 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d84484 q = 1) (hb : d112624 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d84484, d112624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d84484, d112624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d84485 q = 1) (hb : d112625 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d84485, d112625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d84485, d112625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d84486 q = 1) (hb : d112626 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d84486, d112626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d84486, d112626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d84487 q = 1) (hb : d112627 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d84487, d112627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d84487, d112627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d84488 q = 1) (hb : d112628 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d84488, d112628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d84488, d112628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro20909 (p : Pattern) (ha : d84494 p = 1) (hb : d112634 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84489 q = 1) (hb : d112629 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d84489, d112629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84489, d112629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20908 q ha hb
  have h2 (q : Pattern) (ha : d84490 q = 1) (hb : d112630 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d84490, d112630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84490, d112630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d84491 q = 1) (hb : d112631 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d84491, d112631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84491, d112631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d84492 q = 1) (hb : d112632 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d84492, d112632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84492, d112632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d84493 q = 1) (hb : d112633 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d84493, d112633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84493, d112633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84494 q = 1) (hb : d112634 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d84494, d112634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d84494, d112634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20910 (p : Pattern) (ha : d84500 p = 1) (hb : d112640 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d83957 q = 1) (hb : d112521 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d83957, d112521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20879 q ha hb
    | true =>
      simp only [d83957, d112521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20885 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d84090 q = 1) (hb : d112548 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d84090, d112548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84090, d112548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20891 q ha hb
  have h3 (q : Pattern) (ha : d84091 q = 1) (hb : d112549 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d84091, d112549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d84091, d112549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d84224 q = 1) (hb : d112576 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d84224, d112576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84224, d112576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20897 q ha hb
  have h5 (q : Pattern) (ha : d84225 q = 1) (hb : d112577 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d84225, d112577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84225, d112577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d84226 q = 1) (hb : d112578 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d84226, d112578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84226, d112578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d84359 q = 1) (hb : d112605 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d84359, d112605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84359, d112605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20903 q ha hb
  have h8 (q : Pattern) (ha : d84360 q = 1) (hb : d112606 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d84360, d112606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84360, d112606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d84361 q = 1) (hb : d112607 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d84361, d112607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84361, d112607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d84362 q = 1) (hb : d112608 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d84362, d112608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d84362, d112608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d84495 q = 1) (hb : d112635 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d84495, d112635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84495, d112635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20909 q ha hb
  have h12 (q : Pattern) (ha : d84496 q = 1) (hb : d112636 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d84496, d112636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84496, d112636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d84497 q = 1) (hb : d112637 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d84497, d112637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84497, d112637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d84498 q = 1) (hb : d112638 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d84498, d112638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d84498, d112638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d84499 q = 1) (hb : d112639 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d84499, d112639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d84499, d112639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d84500 q = 1) (hb : d112640 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d84500, d112640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d84500, d112640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro20911 (p : Pattern) (ha : d84506 p = 1) (hb : d112646 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84501 q = 1) (hb : d112641 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d84501, d112641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20910 q ha hb
    | true =>
      simp only [d84501, d112641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84502 q = 1) (hb : d112642 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d84502, d112642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84502, d112642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84503 q = 1) (hb : d112643 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d84503, d112643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84503, d112643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84504 q = 1) (hb : d112644 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d84504, d112644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84504, d112644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84505 q = 1) (hb : d112645 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d84505, d112645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84505, d112645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84506 q = 1) (hb : d112646 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d84506, d112646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84506, d112646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20912 (p : Pattern) (ha : d84512 p = 1) (hb : d112652 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84507 q = 1) (hb : d112647 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d84507, d112647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20911 q ha hb
    | true =>
      simp only [d84507, d112647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84508 q = 1) (hb : d112648 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d84508, d112648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84508, d112648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84509 q = 1) (hb : d112649 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d84509, d112649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84509, d112649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84510 q = 1) (hb : d112650 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d84510, d112650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84510, d112650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84511 q = 1) (hb : d112651 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d84511, d112651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84511, d112651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84512 q = 1) (hb : d112652 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d84512, d112652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84512, d112652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20913 (p : Pattern) (ha : d84518 p = 1) (hb : d112658 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84513 q = 1) (hb : d112653 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d84513, d112653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20912 q ha hb
    | true =>
      simp only [d84513, d112653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84514 q = 1) (hb : d112654 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d84514, d112654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84514, d112654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84515 q = 1) (hb : d112655 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d84515, d112655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84515, d112655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84516 q = 1) (hb : d112656 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d84516, d112656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84516, d112656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84517 q = 1) (hb : d112657 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d84517, d112657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84517, d112657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84518 q = 1) (hb : d112658 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d84518, d112658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84518, d112658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20914 (p : Pattern) (ha : d84524 p = 1) (hb : d112664 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84519 q = 1) (hb : d112659 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d84519, d112659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20913 q ha hb
    | true =>
      simp only [d84519, d112659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84520 q = 1) (hb : d112660 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d84520, d112660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84520, d112660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84521 q = 1) (hb : d112661 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d84521, d112661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84521, d112661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84522 q = 1) (hb : d112662 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d84522, d112662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84522, d112662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84523 q = 1) (hb : d112663 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d84523, d112663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84523, d112663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84524 q = 1) (hb : d112664 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d84524, d112664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84524, d112664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20915 (p : Pattern) (ha : d84530 p = 1) (hb : d112670 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84525 q = 1) (hb : d112665 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d84525, d112665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20914 q ha hb
    | true =>
      simp only [d84525, d112665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84526 q = 1) (hb : d112666 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d84526, d112666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84526, d112666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84527 q = 1) (hb : d112667 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d84527, d112667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84527, d112667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84528 q = 1) (hb : d112668 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d84528, d112668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84528, d112668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84529 q = 1) (hb : d112669 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d84529, d112669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84529, d112669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84530 q = 1) (hb : d112670 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d84530, d112670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84530, d112670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20916 (p : Pattern) (ha : d84536 p = 1) (hb : d112676 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84531 q = 1) (hb : d112671 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d84531, d112671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20915 q ha hb
    | true =>
      simp only [d84531, d112671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84532 q = 1) (hb : d112672 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d84532, d112672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84532, d112672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84533 q = 1) (hb : d112673 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d84533, d112673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84533, d112673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84534 q = 1) (hb : d112674 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d84534, d112674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84534, d112674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84535 q = 1) (hb : d112675 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d84535, d112675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84535, d112675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84536 q = 1) (hb : d112676 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d84536, d112676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84536, d112676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20917 (p : Pattern) (ha : d84542 p = 1) (hb : d112682 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d84537 q = 1) (hb : d112677 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d84537, d112677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20916 q ha hb
    | true =>
      simp only [d84537, d112677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d84538 q = 1) (hb : d112678 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d84538, d112678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d84538, d112678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d84539 q = 1) (hb : d112679 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d84539, d112679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d84539, d112679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d84540 q = 1) (hb : d112680 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d84540, d112680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d84540, d112680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d84541 q = 1) (hb : d112681 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d84541, d112681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d84541, d112681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d84542 q = 1) (hb : d112682 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d84542, d112682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d84542, d112682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro20918 (p : Pattern) (ha : d85432 p = 1) (hb : d111718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7318 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7324 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7333 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d111668 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85428 q = 1) (hb : d111714 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85428, d111714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d85428, d111714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d7349 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d85429 q = 1) (hb : d111715 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85429, d111715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85429, d111715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d85430 q = 1) (hb : d111716 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85430, d111716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85430, d111716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85431 q = 1) (hb : d111717 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85431, d111717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85431, d111717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85432 q = 1) (hb : d111718 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85432, d111718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85432, d111718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro20919 (p : Pattern) (ha : d85437 p = 1) (hb : d111725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7318 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7324 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7333 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d111668 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d85428 q = 1) (hb : d111714 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85428, d111714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85428, d111714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d7349 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d85429 q = 1) (hb : d111715 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85429, d111715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85429, d111715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d85430 q = 1) (hb : d111716 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85430, d111716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85430, d111716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85431 q = 1) (hb : d111717 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85431, d111717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85431, d111717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d7358 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d7362 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d7364 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d111675 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d85433 q = 1) (hb : d111721 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85433, d111721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d85433, d111721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d7370 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85434 q = 1) (hb : d111722 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85434, d111722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85434, d111722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85435 q = 1) (hb : d111723 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85435, d111723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d85435, d111723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85436 q = 1) (hb : d111724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85436, d111724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85436, d111724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d85437 q = 1) (hb : d111725 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85437, d111725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85437, d111725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro20920 (p : Pattern) (ha : d85444 p = 1) (hb : d112472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7364 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d111675 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85433 q = 1) (hb : d111721 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85433, d111721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85433, d111721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7370 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85434 q = 1) (hb : d111722 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85434, d111722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85434, d111722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85442 q = 1) (hb : d111723 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85442, d111723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85442, d111723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85443 q = 1) (hb : d111724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85443, d111724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85443, d111724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85444 q = 1) (hb : d112472 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85444, d112472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85444, d112472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20921 (p : Pattern) (ha : d85454 p = 1) (hb : d112482 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7397 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d111697 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85450 q = 1) (hb : d112478 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85450, d112478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85450, d112478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7413 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85451 q = 1) (hb : d112479 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85451, d112479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85451, d112479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85452 q = 1) (hb : d112480 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85452, d112480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85452, d112480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85453 q = 1) (hb : d112481 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85453, d112481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85453, d112481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85454 q = 1) (hb : d112482 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85454, d112482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85454, d112482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20922 (p : Pattern) (ha : d85460 p = 1) (hb : d112488 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7312 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85438 q = 1) (hb : d111726 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85438, d111726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20918 q ha hb
    | true =>
      simp only [d85438, d111726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20919 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7377 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85439 q = 1) (hb : d111727 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85439, d111727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85439, d111727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85440 q = 1) (hb : d112470 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85440, d112470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85440, d112470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85441 q = 1) (hb : d112471 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85441, d112471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85441, d112471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85445 q = 1) (hb : d112473 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85445, d112473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85445, d112473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20920 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d85446 q = 1) (hb : d112474 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85446, d112474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85446, d112474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d85447 q = 1) (hb : d112475 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85447, d112475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85447, d112475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d85448 q = 1) (hb : d112476 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85448, d112476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85448, d112476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d85449 q = 1) (hb : d112477 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85449, d112477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85449, d112477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85455 q = 1) (hb : d112483 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85455, d112483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85455, d112483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20921 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85456 q = 1) (hb : d112484 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85456, d112484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85456, d112484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85457 q = 1) (hb : d112485 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85457, d112485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85457, d112485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d85458 q = 1) (hb : d112486 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85458, d112486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85458, d112486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d85459 q = 1) (hb : d112487 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85459, d112487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85459, d112487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d85460 q = 1) (hb : d112488 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85460, d112488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85460, d112488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro20923 (p : Pattern) (ha : d85466 p = 1) (hb : d112494 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d85423 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d85423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d85423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10216 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d85424 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d85424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d85424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d85425 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d85425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d85425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d85426 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d85426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d85426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d85427 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d85427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d85427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85461 q = 1) (hb : d112489 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85461, d112489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85461, d112489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20922 q ha hb
  have h8 (q : Pattern) (ha : d85462 q = 1) (hb : d112490 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85462, d112490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85462, d112490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85463 q = 1) (hb : d112491 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85463, d112491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85463, d112491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85464 q = 1) (hb : d112492 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85464, d112492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85464, d112492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d85465 q = 1) (hb : d112493 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85465, d112493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85465, d112493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d85466 q = 1) (hb : d112494 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85466, d112494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d85466, d112494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro20924 (p : Pattern) (ha : d85471 p = 1) (hb : d111811 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7457 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7463 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7472 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d111806 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85467 q = 1) (hb : d111807 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85467, d111807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d85467, d111807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d7488 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d85468 q = 1) (hb : d111808 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85468, d111808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85468, d111808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d85469 q = 1) (hb : d111809 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85469, d111809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85469, d111809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85470 q = 1) (hb : d111810 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85470, d111810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85470, d111810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85471 q = 1) (hb : d111811 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85471, d111811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85471, d111811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro20925 (p : Pattern) (ha : d85476 p = 1) (hb : d111819 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7457 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7463 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7472 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d111806 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d85467 q = 1) (hb : d111807 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85467, d111807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85467, d111807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d7488 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d85468 q = 1) (hb : d111808 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85468, d111808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85468, d111808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d85469 q = 1) (hb : d111809 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85469, d111809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85469, d111809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85470 q = 1) (hb : d111810 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85470, d111810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85470, d111810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d7497 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d7501 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d7503 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d111814 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d85472 q = 1) (hb : d111815 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85472, d111815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d85472, d111815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d7509 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85473 q = 1) (hb : d111816 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85473, d111816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85473, d111816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85474 q = 1) (hb : d111817 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85474, d111817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d85474, d111817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85475 q = 1) (hb : d111818 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85475, d111818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85475, d111818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d85476 q = 1) (hb : d111819 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85476, d111819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85476, d111819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro20926 (p : Pattern) (ha : d85483 p = 1) (hb : d112497 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7503 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d111814 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85472 q = 1) (hb : d111815 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85472, d111815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85472, d111815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7509 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85473 q = 1) (hb : d111816 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85473, d111816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85473, d111816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85481 q = 1) (hb : d111817 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85481, d111817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85481, d111817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85482 q = 1) (hb : d111818 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85482, d111818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85482, d111818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85483 q = 1) (hb : d112497 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85483, d112497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85483, d112497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20927 (p : Pattern) (ha : d85493 p = 1) (hb : d112508 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7540 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112503 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85489 q = 1) (hb : d112504 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85489, d112504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85489, d112504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7556 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85490 q = 1) (hb : d112505 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85490, d112505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85490, d112505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85491 q = 1) (hb : d112506 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85491, d112506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85491, d112506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85492 q = 1) (hb : d112507 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85492, d112507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85492, d112507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85493 q = 1) (hb : d112508 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85493, d112508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85493, d112508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20928 (p : Pattern) (ha : d85499 p = 1) (hb : d112514 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7451 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85477 q = 1) (hb : d111820 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85477, d111820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20924 q ha hb
    | true =>
      simp only [d85477, d111820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20925 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7516 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85478 q = 1) (hb : d111821 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85478, d111821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85478, d111821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85479 q = 1) (hb : d112495 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85479, d112495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85479, d112495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85480 q = 1) (hb : d112496 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85480, d112496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85480, d112496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85484 q = 1) (hb : d112498 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85484, d112498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85484, d112498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20926 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d654 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d85485 q = 1) (hb : d112499 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85485, d112499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85485, d112499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d85486 q = 1) (hb : d112500 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85486, d112500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85486, d112500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d85487 q = 1) (hb : d112501 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85487, d112501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85487, d112501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d85488 q = 1) (hb : d112502 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85488, d112502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85488, d112502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85494 q = 1) (hb : d112509 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85494, d112509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85494, d112509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20927 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d737 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85495 q = 1) (hb : d112510 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85495, d112510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85495, d112510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85496 q = 1) (hb : d112511 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85496, d112511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85496, d112511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d85497 q = 1) (hb : d112512 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85497, d112512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85497, d112512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d85498 q = 1) (hb : d112513 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85498, d112513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85498, d112513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d85499 q = 1) (hb : d112514 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85499, d112514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85499, d112514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro20929 (p : Pattern) (ha : d85505 p = 1) (hb : d112520 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85500 q = 1) (hb : d112515 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85500, d112515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85500, d112515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20928 q ha hb
  have h2 (q : Pattern) (ha : d85501 q = 1) (hb : d112516 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85501, d112516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85501, d112516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85502 q = 1) (hb : d112517 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85502, d112517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85502, d112517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85503 q = 1) (hb : d112518 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85503, d112518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85503, d112518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85504 q = 1) (hb : d112519 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85504, d112519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85504, d112519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85505 q = 1) (hb : d112520 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85505, d112520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85505, d112520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20930 (p : Pattern) (ha : d85511 p = 1) (hb : d111930 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7605 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7611 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7620 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d111925 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85507 q = 1) (hb : d111926 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85507, d111926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d85507, d111926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d7636 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d85508 q = 1) (hb : d111927 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85508, d111927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85508, d111927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d85509 q = 1) (hb : d111928 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85509, d111928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85509, d111928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85510 q = 1) (hb : d111929 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85510, d111929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85510, d111929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85511 q = 1) (hb : d111930 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85511, d111930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85511, d111930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro20931 (p : Pattern) (ha : d85516 p = 1) (hb : d111939 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7605 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7611 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7620 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d111925 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d85507 q = 1) (hb : d111926 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85507, d111926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85507, d111926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d7636 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d85508 q = 1) (hb : d111927 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85508, d111927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85508, d111927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d85509 q = 1) (hb : d111928 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85509, d111928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85509, d111928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85510 q = 1) (hb : d111929 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85510, d111929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85510, d111929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d7645 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d7649 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d7651 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d111934 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d85512 q = 1) (hb : d111935 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85512, d111935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d85512, d111935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d7657 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85513 q = 1) (hb : d111936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85513, d111936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85513, d111936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85514 q = 1) (hb : d111937 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85514, d111937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d85514, d111937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85515 q = 1) (hb : d111938 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85515, d111938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85515, d111938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d85516 q = 1) (hb : d111939 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85516, d111939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85516, d111939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro20932 (p : Pattern) (ha : d85523 p = 1) (hb : d112524 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7651 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d111934 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85512 q = 1) (hb : d111935 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85512, d111935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85512, d111935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7657 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85513 q = 1) (hb : d111936 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85513, d111936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85513, d111936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85521 q = 1) (hb : d111937 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85521, d111937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85521, d111937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85522 q = 1) (hb : d111938 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85522, d111938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85522, d111938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85523 q = 1) (hb : d112524 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85523, d112524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85523, d112524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20933 (p : Pattern) (ha : d85533 p = 1) (hb : d112535 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7692 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112530 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85529 q = 1) (hb : d112531 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85529, d112531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85529, d112531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7708 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85530 q = 1) (hb : d112532 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85530, d112532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85530, d112532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85531 q = 1) (hb : d112533 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85531, d112533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85531, d112533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85532 q = 1) (hb : d112534 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85532, d112534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85532, d112534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85533 q = 1) (hb : d112535 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85533, d112535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85533, d112535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20934 (p : Pattern) (ha : d85539 p = 1) (hb : d112541 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7599 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85517 q = 1) (hb : d111940 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85517, d111940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20930 q ha hb
    | true =>
      simp only [d85517, d111940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20931 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7664 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85518 q = 1) (hb : d111941 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85518, d111941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85518, d111941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85519 q = 1) (hb : d112522 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85519, d112522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85519, d112522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85520 q = 1) (hb : d112523 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85520, d112523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85520, d112523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85524 q = 1) (hb : d112525 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85524, d112525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85524, d112525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20932 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d960 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d85525 q = 1) (hb : d112526 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85525, d112526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85525, d112526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d85526 q = 1) (hb : d112527 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85526, d112527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85526, d112527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d85527 q = 1) (hb : d112528 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85527, d112528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85527, d112528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d85528 q = 1) (hb : d112529 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85528, d112529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85528, d112529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85534 q = 1) (hb : d112536 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85534, d112536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85534, d112536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20933 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1070 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85535 q = 1) (hb : d112537 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85535, d112537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85535, d112537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85536 q = 1) (hb : d112538 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85536, d112538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85536, d112538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d85537 q = 1) (hb : d112539 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85537, d112539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85537, d112539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d85538 q = 1) (hb : d112540 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85538, d112540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85538, d112540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d85539 q = 1) (hb : d112541 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85539, d112541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85539, d112541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro20935 (p : Pattern) (ha : d85545 p = 1) (hb : d112547 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85540 q = 1) (hb : d112542 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85540, d112542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85540, d112542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20934 q ha hb
  have h2 (q : Pattern) (ha : d85541 q = 1) (hb : d112543 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85541, d112543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85541, d112543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85542 q = 1) (hb : d112544 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85542, d112544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85542, d112544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85543 q = 1) (hb : d112545 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85543, d112545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85543, d112545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85544 q = 1) (hb : d112546 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85544, d112546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85544, d112546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85545 q = 1) (hb : d112547 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85545, d112547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85545, d112547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20936 (p : Pattern) (ha : d85552 p = 1) (hb : d112055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7758 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7764 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7773 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112050 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85548 q = 1) (hb : d112051 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85548, d112051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d85548, d112051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d7789 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d85549 q = 1) (hb : d112052 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85549, d112052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85549, d112052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d85550 q = 1) (hb : d112053 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85550, d112053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85550, d112053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85551 q = 1) (hb : d112054 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85551, d112054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85551, d112054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85552 q = 1) (hb : d112055 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85552, d112055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85552, d112055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro20937 (p : Pattern) (ha : d85557 p = 1) (hb : d112064 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7758 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7764 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7773 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112050 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d85548 q = 1) (hb : d112051 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85548, d112051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85548, d112051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d7789 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d85549 q = 1) (hb : d112052 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85549, d112052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85549, d112052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d85550 q = 1) (hb : d112053 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85550, d112053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85550, d112053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85551 q = 1) (hb : d112054 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85551, d112054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85551, d112054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d7798 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d7802 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d7804 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d112059 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d85553 q = 1) (hb : d112060 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85553, d112060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d85553, d112060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d7810 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85554 q = 1) (hb : d112061 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85554, d112061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85554, d112061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85555 q = 1) (hb : d112062 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85555, d112062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d85555, d112062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85556 q = 1) (hb : d112063 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85556, d112063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85556, d112063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d85557 q = 1) (hb : d112064 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85557, d112064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85557, d112064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro20938 (p : Pattern) (ha : d85564 p = 1) (hb : d112552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7804 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112059 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85553 q = 1) (hb : d112060 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85553, d112060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85553, d112060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7810 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85554 q = 1) (hb : d112061 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85554, d112061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85554, d112061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85562 q = 1) (hb : d112062 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85562, d112062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85562, d112062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85563 q = 1) (hb : d112063 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85563, d112063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85563, d112063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85564 q = 1) (hb : d112552 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85564, d112552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85564, d112552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20939 (p : Pattern) (ha : d85574 p = 1) (hb : d112563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7845 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112558 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85570 q = 1) (hb : d112559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85570, d112559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85570, d112559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7861 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85571 q = 1) (hb : d112560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85571, d112560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85571, d112560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85572 q = 1) (hb : d112561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85572, d112561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85572, d112561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85573 q = 1) (hb : d112562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85573, d112562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85573, d112562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85574 q = 1) (hb : d112563 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85574, d112563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85574, d112563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20940 (p : Pattern) (ha : d85580 p = 1) (hb : d112569 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7752 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85558 q = 1) (hb : d112065 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85558, d112065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20936 q ha hb
    | true =>
      simp only [d85558, d112065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20937 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7817 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85559 q = 1) (hb : d112066 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85559, d112066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85559, d112066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85560 q = 1) (hb : d112550 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85560, d112550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85560, d112550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85561 q = 1) (hb : d112551 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85561, d112551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85561, d112551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85565 q = 1) (hb : d112553 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85565, d112553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85565, d112553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20938 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1371 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d85566 q = 1) (hb : d112554 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85566, d112554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85566, d112554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d85567 q = 1) (hb : d112555 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85567, d112555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85567, d112555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d85568 q = 1) (hb : d112556 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85568, d112556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85568, d112556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d85569 q = 1) (hb : d112557 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85569, d112557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85569, d112557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85575 q = 1) (hb : d112564 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85575, d112564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85575, d112564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20939 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1504 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85576 q = 1) (hb : d112565 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85576, d112565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85576, d112565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85577 q = 1) (hb : d112566 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85577, d112566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85577, d112566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d85578 q = 1) (hb : d112567 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85578, d112567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85578, d112567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d85579 q = 1) (hb : d112568 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85579, d112568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85579, d112568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d85580 q = 1) (hb : d112569 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85580, d112569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85580, d112569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro20941 (p : Pattern) (ha : d85586 p = 1) (hb : d112575 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85581 q = 1) (hb : d112570 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85581, d112570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85581, d112570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20940 q ha hb
  have h2 (q : Pattern) (ha : d85582 q = 1) (hb : d112571 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85582, d112571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85582, d112571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85583 q = 1) (hb : d112572 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85583, d112572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85583, d112572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85584 q = 1) (hb : d112573 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85584, d112573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85584, d112573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85585 q = 1) (hb : d112574 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85585, d112574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85585, d112574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85586 q = 1) (hb : d112575 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85586, d112575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85586, d112575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20942 (p : Pattern) (ha : d85594 p = 1) (hb : d112181 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7912 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7918 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d7927 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112176 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85590 q = 1) (hb : d112177 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85590, d112177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d85590, d112177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d7943 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d85591 q = 1) (hb : d112178 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85591, d112178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85591, d112178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d85592 q = 1) (hb : d112179 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85592, d112179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85592, d112179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85593 q = 1) (hb : d112180 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85593, d112180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85593, d112180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85594 q = 1) (hb : d112181 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85594, d112181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85594, d112181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro20943 (p : Pattern) (ha : d85599 p = 1) (hb : d112190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7912 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7918 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7927 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112176 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d85590 q = 1) (hb : d112177 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85590, d112177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85590, d112177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d7943 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d85591 q = 1) (hb : d112178 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85591, d112178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85591, d112178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d85592 q = 1) (hb : d112179 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85592, d112179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85592, d112179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85593 q = 1) (hb : d112180 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85593, d112180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85593, d112180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d7952 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d7956 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d7958 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d112185 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d85595 q = 1) (hb : d112186 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85595, d112186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d85595, d112186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d7964 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85596 q = 1) (hb : d112187 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85596, d112187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85596, d112187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85597 q = 1) (hb : d112188 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85597, d112188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d85597, d112188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85598 q = 1) (hb : d112189 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85598, d112189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85598, d112189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d85599 q = 1) (hb : d112190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85599, d112190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85599, d112190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro20944 (p : Pattern) (ha : d85606 p = 1) (hb : d112581 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7958 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112185 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85595 q = 1) (hb : d112186 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85595, d112186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85595, d112186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d7964 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85596 q = 1) (hb : d112187 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85596, d112187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85596, d112187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85604 q = 1) (hb : d112188 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85604, d112188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85604, d112188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85605 q = 1) (hb : d112189 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85605, d112189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85605, d112189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85606 q = 1) (hb : d112581 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85606, d112581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85606, d112581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20945 (p : Pattern) (ha : d85616 p = 1) (hb : d112592 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7999 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112587 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85612 q = 1) (hb : d112588 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85612, d112588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85612, d112588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8015 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85613 q = 1) (hb : d112589 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85613, d112589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85613, d112589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85614 q = 1) (hb : d112590 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85614, d112590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85614, d112590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85615 q = 1) (hb : d112591 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85615, d112591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85615, d112591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85616 q = 1) (hb : d112592 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85616, d112592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85616, d112592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20946 (p : Pattern) (ha : d85622 p = 1) (hb : d112598 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7906 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85600 q = 1) (hb : d112191 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85600, d112191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20942 q ha hb
    | true =>
      simp only [d85600, d112191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20943 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7971 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85601 q = 1) (hb : d112192 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85601, d112192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85601, d112192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85602 q = 1) (hb : d112579 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85602, d112579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85602, d112579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85603 q = 1) (hb : d112580 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85603, d112580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85603, d112580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85607 q = 1) (hb : d112582 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85607, d112582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85607, d112582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20944 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1848 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d85608 q = 1) (hb : d112583 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85608, d112583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85608, d112583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d85609 q = 1) (hb : d112584 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85609, d112584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85609, d112584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d85610 q = 1) (hb : d112585 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85610, d112585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85610, d112585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d85611 q = 1) (hb : d112586 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85611, d112586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85611, d112586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85617 q = 1) (hb : d112593 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85617, d112593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85617, d112593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20945 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1981 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85618 q = 1) (hb : d112594 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85618, d112594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85618, d112594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85619 q = 1) (hb : d112595 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85619, d112595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85619, d112595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d85620 q = 1) (hb : d112596 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85620, d112596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85620, d112596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d85621 q = 1) (hb : d112597 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85621, d112597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85621, d112597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d85622 q = 1) (hb : d112598 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85622, d112598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85622, d112598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro20947 (p : Pattern) (ha : d85628 p = 1) (hb : d112604 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85623 q = 1) (hb : d112599 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85623, d112599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85623, d112599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20946 q ha hb
  have h2 (q : Pattern) (ha : d85624 q = 1) (hb : d112600 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85624, d112600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85624, d112600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85625 q = 1) (hb : d112601 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85625, d112601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85625, d112601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85626 q = 1) (hb : d112602 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85626, d112602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85626, d112602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85627 q = 1) (hb : d112603 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85627, d112603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85627, d112603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85628 q = 1) (hb : d112604 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85628, d112604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85628, d112604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20948 (p : Pattern) (ha : d85637 p = 1) (hb : d112308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8067 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8073 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d8082 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d112303 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85633 q = 1) (hb : d112304 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85633, d112304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d85633, d112304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d8098 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d85634 q = 1) (hb : d112305 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85634, d112305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85634, d112305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d85635 q = 1) (hb : d112306 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85635, d112306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85635, d112306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85636 q = 1) (hb : d112307 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85636, d112307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85636, d112307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85637 q = 1) (hb : d112308 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85637, d112308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85637, d112308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro20949 (p : Pattern) (ha : d85642 p = 1) (hb : d112317 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8067 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8073 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8082 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d112303 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d85633 q = 1) (hb : d112304 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85633, d112304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85633, d112304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d8098 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d85634 q = 1) (hb : d112305 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85634, d112305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85634, d112305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d85635 q = 1) (hb : d112306 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85635, d112306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85635, d112306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85636 q = 1) (hb : d112307 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85636, d112307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85636, d112307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d8107 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d8111 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d8113 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d112312 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d85638 q = 1) (hb : d112313 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85638, d112313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d85638, d112313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d8119 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85639 q = 1) (hb : d112314 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85639, d112314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85639, d112314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85640 q = 1) (hb : d112315 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85640, d112315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d85640, d112315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d85641 q = 1) (hb : d112316 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85641, d112316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85641, d112316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d85642 q = 1) (hb : d112317 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85642, d112317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85642, d112317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro20950 (p : Pattern) (ha : d85649 p = 1) (hb : d112611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8113 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112312 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85638 q = 1) (hb : d112313 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85638, d112313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85638, d112313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8119 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85639 q = 1) (hb : d112314 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85639, d112314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85639, d112314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85647 q = 1) (hb : d112315 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85647, d112315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85647, d112315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85648 q = 1) (hb : d112316 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85648, d112316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85648, d112316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85649 q = 1) (hb : d112611 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85649, d112611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85649, d112611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20951 (p : Pattern) (ha : d85659 p = 1) (hb : d112622 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8154 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112617 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85655 q = 1) (hb : d112618 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85655, d112618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85655, d112618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d8170 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85656 q = 1) (hb : d112619 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85656, d112619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85656, d112619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d85657 q = 1) (hb : d112620 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85657, d112620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85657, d112620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85658 q = 1) (hb : d112621 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85658, d112621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85658, d112621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d85659 q = 1) (hb : d112622 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85659, d112622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85659, d112622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20952 (p : Pattern) (ha : d85665 p = 1) (hb : d112628 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8061 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85643 q = 1) (hb : d112318 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85643, d112318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20948 q ha hb
    | true =>
      simp only [d85643, d112318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20949 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8126 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d85644 q = 1) (hb : d112319 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85644, d112319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85644, d112319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d85645 q = 1) (hb : d112609 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85645, d112609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85645, d112609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85646 q = 1) (hb : d112610 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85646, d112610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85646, d112610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85650 q = 1) (hb : d112612 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85650, d112612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85650, d112612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20950 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d2326 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d85651 q = 1) (hb : d112613 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85651, d112613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85651, d112613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d85652 q = 1) (hb : d112614 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85652, d112614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85652, d112614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d85653 q = 1) (hb : d112615 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85653, d112615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85653, d112615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d85654 q = 1) (hb : d112616 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85654, d112616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85654, d112616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85660 q = 1) (hb : d112623 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85660, d112623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85660, d112623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20951 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d2459 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d85661 q = 1) (hb : d112624 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85661, d112624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85661, d112624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d85662 q = 1) (hb : d112625 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85662, d112625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85662, d112625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d85663 q = 1) (hb : d112626 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85663, d112626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85663, d112626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d85664 q = 1) (hb : d112627 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85664, d112627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85664, d112627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d85665 q = 1) (hb : d112628 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85665, d112628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85665, d112628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro20953 (p : Pattern) (ha : d85671 p = 1) (hb : d112634 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85666 q = 1) (hb : d112629 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85666, d112629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85666, d112629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20952 q ha hb
  have h2 (q : Pattern) (ha : d85667 q = 1) (hb : d112630 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85667, d112630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85667, d112630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d85668 q = 1) (hb : d112631 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85668, d112631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85668, d112631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85669 q = 1) (hb : d112632 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85669, d112632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85669, d112632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d85670 q = 1) (hb : d112633 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85670, d112633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85670, d112633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85671 q = 1) (hb : d112634 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85671, d112634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85671, d112634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20954 (p : Pattern) (ha : d85677 p = 1) (hb : d112640 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d85506 q = 1) (hb : d112521 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85506, d112521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20923 q ha hb
    | true =>
      simp only [d85506, d112521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20929 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d85546 q = 1) (hb : d112548 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85546, d112548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85546, d112548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20935 q ha hb
  have h3 (q : Pattern) (ha : d85547 q = 1) (hb : d112549 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d85547, d112549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85547, d112549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d85587 q = 1) (hb : d112576 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85587, d112576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85587, d112576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20941 q ha hb
  have h5 (q : Pattern) (ha : d85588 q = 1) (hb : d112577 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d85588, d112577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85588, d112577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85589 q = 1) (hb : d112578 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d85589, d112578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85589, d112578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d85629 q = 1) (hb : d112605 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85629, d112605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85629, d112605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20947 q ha hb
  have h8 (q : Pattern) (ha : d85630 q = 1) (hb : d112606 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d85630, d112606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85630, d112606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d85631 q = 1) (hb : d112607 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d85631, d112607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85631, d112607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d85632 q = 1) (hb : d112608 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d85632, d112608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85632, d112608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d85672 q = 1) (hb : d112635 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85672, d112635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85672, d112635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20953 q ha hb
  have h12 (q : Pattern) (ha : d85673 q = 1) (hb : d112636 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d85673, d112636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85673, d112636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d85674 q = 1) (hb : d112637 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d85674, d112637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85674, d112637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d85675 q = 1) (hb : d112638 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d85675, d112638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85675, d112638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d85676 q = 1) (hb : d112639 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d85676, d112639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85676, d112639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d85677 q = 1) (hb : d112640 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d85677, d112640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85677, d112640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro20955 (p : Pattern) (ha : d85683 p = 1) (hb : d112646 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85678 q = 1) (hb : d112641 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d85678, d112641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20954 q ha hb
    | true =>
      simp only [d85678, d112641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85679 q = 1) (hb : d112642 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d85679, d112642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85679, d112642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85680 q = 1) (hb : d112643 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d85680, d112643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85680, d112643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85681 q = 1) (hb : d112644 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d85681, d112644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85681, d112644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85682 q = 1) (hb : d112645 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d85682, d112645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85682, d112645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85683 q = 1) (hb : d112646 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d85683, d112646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85683, d112646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20956 (p : Pattern) (ha : d85689 p = 1) (hb : d112652 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85684 q = 1) (hb : d112647 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d85684, d112647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20955 q ha hb
    | true =>
      simp only [d85684, d112647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85685 q = 1) (hb : d112648 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d85685, d112648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85685, d112648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85686 q = 1) (hb : d112649 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d85686, d112649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85686, d112649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85687 q = 1) (hb : d112650 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d85687, d112650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85687, d112650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85688 q = 1) (hb : d112651 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d85688, d112651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85688, d112651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85689 q = 1) (hb : d112652 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d85689, d112652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85689, d112652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20957 (p : Pattern) (ha : d85695 p = 1) (hb : d112658 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85690 q = 1) (hb : d112653 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d85690, d112653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20956 q ha hb
    | true =>
      simp only [d85690, d112653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85691 q = 1) (hb : d112654 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d85691, d112654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85691, d112654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85692 q = 1) (hb : d112655 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d85692, d112655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85692, d112655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85693 q = 1) (hb : d112656 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d85693, d112656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85693, d112656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85694 q = 1) (hb : d112657 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d85694, d112657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85694, d112657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85695 q = 1) (hb : d112658 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d85695, d112658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85695, d112658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20958 (p : Pattern) (ha : d85701 p = 1) (hb : d112664 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85696 q = 1) (hb : d112659 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d85696, d112659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20957 q ha hb
    | true =>
      simp only [d85696, d112659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85697 q = 1) (hb : d112660 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d85697, d112660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85697, d112660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85698 q = 1) (hb : d112661 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d85698, d112661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85698, d112661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85699 q = 1) (hb : d112662 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d85699, d112662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85699, d112662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85700 q = 1) (hb : d112663 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d85700, d112663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85700, d112663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85701 q = 1) (hb : d112664 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d85701, d112664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85701, d112664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20959 (p : Pattern) (ha : d85707 p = 1) (hb : d112670 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85702 q = 1) (hb : d112665 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d85702, d112665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20958 q ha hb
    | true =>
      simp only [d85702, d112665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85703 q = 1) (hb : d112666 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d85703, d112666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85703, d112666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85704 q = 1) (hb : d112667 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d85704, d112667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85704, d112667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85705 q = 1) (hb : d112668 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d85705, d112668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85705, d112668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85706 q = 1) (hb : d112669 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d85706, d112669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85706, d112669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85707 q = 1) (hb : d112670 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d85707, d112670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85707, d112670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20960 (p : Pattern) (ha : d85713 p = 1) (hb : d112676 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85708 q = 1) (hb : d112671 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d85708, d112671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20959 q ha hb
    | true =>
      simp only [d85708, d112671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85709 q = 1) (hb : d112672 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d85709, d112672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85709, d112672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85710 q = 1) (hb : d112673 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d85710, d112673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85710, d112673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85711 q = 1) (hb : d112674 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d85711, d112674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85711, d112674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85712 q = 1) (hb : d112675 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d85712, d112675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85712, d112675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85713 q = 1) (hb : d112676 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d85713, d112676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85713, d112676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20961 (p : Pattern) (ha : d85719 p = 1) (hb : d112682 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d85714 q = 1) (hb : d112677 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d85714, d112677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20960 q ha hb
    | true =>
      simp only [d85714, d112677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d85715 q = 1) (hb : d112678 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d85715, d112678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85715, d112678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d85716 q = 1) (hb : d112679 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d85716, d112679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85716, d112679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85717 q = 1) (hb : d112680 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d85717, d112680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85717, d112680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85718 q = 1) (hb : d112681 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d85718, d112681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85718, d112681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d85719 q = 1) (hb : d112682 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d85719, d112682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85719, d112682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20962 (p : Pattern) (ha : d6739 p = 1) (hb : d104544 p = 1) : d88140 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d475 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d34 q = 1) (hb : d92313 q = 1) : d34 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6738 q = 1) (hb : d104544 q = 1) : d88139 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6738, d104544, d88139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6738, d104544, d88139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6739 q = 1) (hb : d104544 q = 1) : d88140 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6739, d88140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6739, d88140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro20963 (p : Pattern) (ha : d8238 p = 1) (hb : d104544 p = 1) : d88146 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d104544 q = 1) : d88141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20962 q ha hb
    | true =>
      simp only [d6740, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d104544 q = 1) : d88142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14693 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8235 q = 1) (hb : d104544 q = 1) : d88143 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8235, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8236 q = 1) (hb : d104544 q = 1) : d88144 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8236, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8236, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8237 q = 1) (hb : d104544 q = 1) : d88145 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8237, d88145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8237, d88145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8238 q = 1) (hb : d104544 q = 1) : d88146 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8238, d88146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8238, d88146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20964 (p : Pattern) (ha : d94191 p = 1) (hb : d104544 p = 1) : d88152 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14712 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14713 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8239 q = 1) (hb : d104544 q = 1) : d88147 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8239, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20963 q ha hb
    | true =>
      simp only [d8239, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14694 q ha hb
  have h9 (q : Pattern) (ha : d94187 q = 1) (hb : d104544 q = 1) : d88148 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94187, d88148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94187, d88148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14694 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94188 q = 1) (hb : d104544 q = 1) : d88149 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94188, d88149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94188, d88149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94189 q = 1) (hb : d104544 q = 1) : d88150 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94189, d88150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94189, d88150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94190 q = 1) (hb : d104544 q = 1) : d88151 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94190, d88151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94190, d88151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94191 q = 1) (hb : d104544 q = 1) : d88152 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94191, d88152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94191, d88152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro20965 (p : Pattern) (ha : d8245 p = 1) (hb : d104544 p = 1) : d88153 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d104544 q = 1) : d88141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20962 q ha hb
    | true =>
      simp only [d6740, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d104544 q = 1) : d88142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14693 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8235 q = 1) (hb : d104544 q = 1) : d88143 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8235, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8236 q = 1) (hb : d104544 q = 1) : d88144 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8236, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8236, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8237 q = 1) (hb : d104544 q = 1) : d88145 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8237, d88145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8237, d88145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8245 q = 1) (hb : d104544 q = 1) : d88153 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8245, d88153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8245, d88153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro20966 (p : Pattern) (ha : d94196 p = 1) (hb : d104544 p = 1) : d88159 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d117 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14712 q ha hb
    | true =>
      simp only [d117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d118 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d119 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d120 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d124 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14713 q ha hb
    | true =>
      simp only [d124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d125 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8239 q = 1) (hb : d104544 q = 1) : d88147 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8239, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20963 q ha hb
    | true =>
      simp only [d8239, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14694 q ha hb
  have h9 (q : Pattern) (ha : d94187 q = 1) (hb : d104544 q = 1) : d88148 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94187, d88148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94187, d88148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d43 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14694 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d44 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94188 q = 1) (hb : d104544 q = 1) : d88149 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94188, d88149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94188, d88149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94189 q = 1) (hb : d104544 q = 1) : d88150 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94189, d88150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94189, d88150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94190 q = 1) (hb : d104544 q = 1) : d88151 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94190, d88151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94190, d88151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d195 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14716 q ha hb
    | true =>
      simp only [d195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d196 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d197 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d198 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d200 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14717 q ha hb
    | true =>
      simp only [d200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d201 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d202 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d8246 q = 1) (hb : d104544 q = 1) : d88154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8246, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20965 q ha hb
    | true =>
      simp only [d8246, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14696 q ha hb
  have h23 (q : Pattern) (ha : d94192 q = 1) (hb : d104544 q = 1) : d88155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94192, d88155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d94192, d88155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d50 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14696 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d51 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d94193 q = 1) (hb : d104544 q = 1) : d88156 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94193, d88156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d94193, d88156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d94194 q = 1) (hb : d104544 q = 1) : d88157 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94194, d88157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94194, d88157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d94195 q = 1) (hb : d104544 q = 1) : d88158 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94195, d88158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d94195, d88158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d94196 q = 1) (hb : d104544 q = 1) : d88159 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94196, d88159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94196, d88159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro20967 (p : Pattern) (ha : d94203 p = 1) (hb : d104544 p = 1) : d88164 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8246 q = 1) (hb : d104544 q = 1) : d88154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8246, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20965 q ha hb
    | true =>
      simp only [d8246, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14696 q ha hb
  have h2 (q : Pattern) (ha : d94192 q = 1) (hb : d104544 q = 1) : d88155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94192, d88155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94192, d88155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d50 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14696 q ha hb
    | true =>
      simp only [d50, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94193 q = 1) (hb : d104544 q = 1) : d88156 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94193, d88156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94193, d88156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94201 q = 1) (hb : d104544 q = 1) : d88157 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94201, d88157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94201, d88157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94202 q = 1) (hb : d104544 q = 1) : d88158 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94202, d88158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94202, d88158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94203 q = 1) (hb : d104544 q = 1) : d88164 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94203, d88164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94203, d88164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20968 (p : Pattern) (ha : d6772 p = 1) (hb : d104544 p = 1) : d88171 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d673 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d75 q = 1) (hb : d92313 q = 1) : d75 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6771 q = 1) (hb : d104544 q = 1) : d88170 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6771, d104544, d88170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6771, d104544, d88170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6772 q = 1) (hb : d104544 q = 1) : d88171 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6772, d88171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6772, d88171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro20969 (p : Pattern) (ha : d8267 p = 1) (hb : d104544 p = 1) : d88177 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6773 q = 1) (hb : d104544 q = 1) : d88172 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6773, d88172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20968 q ha hb
    | true =>
      simp only [d6773, d88172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6774 q = 1) (hb : d104544 q = 1) : d88173 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6774, d88173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6774, d88173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14699 q ha hb
    | true =>
      simp only [d78, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d79 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8264 q = 1) (hb : d104544 q = 1) : d88174 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8264, d88174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8264, d88174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8265 q = 1) (hb : d104544 q = 1) : d88175 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8265, d88175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8265, d88175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8266 q = 1) (hb : d104544 q = 1) : d88176 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8266, d88176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8266, d88176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8267 q = 1) (hb : d104544 q = 1) : d88177 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8267, d88177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8267, d88177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro20970 (p : Pattern) (ha : d94213 p = 1) (hb : d104544 p = 1) : d88183 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8268 q = 1) (hb : d104544 q = 1) : d88178 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8268, d88178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20969 q ha hb
    | true =>
      simp only [d8268, d88178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14700 q ha hb
  have h2 (q : Pattern) (ha : d94209 q = 1) (hb : d104544 q = 1) : d88179 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94209, d88179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94209, d88179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d84 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14700 q ha hb
    | true =>
      simp only [d84, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94210 q = 1) (hb : d104544 q = 1) : d88180 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94210, d88180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94210, d88180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94211 q = 1) (hb : d104544 q = 1) : d88181 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94211, d88181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94211, d88181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94212 q = 1) (hb : d104544 q = 1) : d88182 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94212, d88182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94212, d88182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94213 q = 1) (hb : d104544 q = 1) : d88183 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94213, d88183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94213, d88183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20971 (p : Pattern) (ha : d94219 p = 1) (hb : d104544 p = 1) : d88189 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14703 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14703 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14704 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94197 q = 1) (hb : d104544 q = 1) : d88160 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94197, d88160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20964 q ha hb
    | true =>
      simp only [d94197, d88160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20966 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14705 q ha hb
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d94198 q = 1) (hb : d104544 q = 1) : d88161 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94198, d88161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94198, d88161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94199 q = 1) (hb : d104544 q = 1) : d88162 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94199, d88162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94199, d88162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d94200 q = 1) (hb : d104544 q = 1) : d88163 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94200, d88163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94200, d88163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94204 q = 1) (hb : d104544 q = 1) : d88165 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94204, d88165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94204, d88165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20967 q ha hb
  have h12 (q : Pattern) (ha : d94205 q = 1) (hb : d104544 q = 1) : d88166 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94205, d88166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94205, d88166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d94206 q = 1) (hb : d104544 q = 1) : d88167 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94206, d88167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d94206, d88167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d94207 q = 1) (hb : d104544 q = 1) : d88168 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94207, d88168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94207, d88168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94208 q = 1) (hb : d104544 q = 1) : d88169 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94208, d88169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94208, d88169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d94214 q = 1) (hb : d104544 q = 1) : d88184 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94214, d88184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94214, d88184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20970 q ha hb
  have h17 (q : Pattern) (ha : d94215 q = 1) (hb : d104544 q = 1) : d88185 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94215, d88185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94215, d88185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d94216 q = 1) (hb : d104544 q = 1) : d88186 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94216, d88186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94216, d88186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d94217 q = 1) (hb : d104544 q = 1) : d88187 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94217, d88187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d94217, d88187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d94218 q = 1) (hb : d104544 q = 1) : d88188 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94218, d88188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d94218, d88188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d94219 q = 1) (hb : d104544 q = 1) : d88189 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94219, d88189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d94219, d88189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro20972 (p : Pattern) (ha : d8289 p = 1) (hb : d104544 p = 1) : d88199 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8239 q = 1) (hb : d104544 q = 1) : d88147 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8239, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20963 q ha hb
    | true =>
      simp only [d8239, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14694 q ha hb
  have h2 (q : Pattern) (ha : d8285 q = 1) (hb : d104544 q = 1) : d88195 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8285, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8285, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8286 q = 1) (hb : d104544 q = 1) : d88196 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8286, d88196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8286, d88196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8287 q = 1) (hb : d104544 q = 1) : d88197 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8287, d88197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8287, d88197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8288 q = 1) (hb : d104544 q = 1) : d88198 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8288, d88198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8288, d88198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8289 q = 1) (hb : d104544 q = 1) : d88199 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8289, d88199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8289, d88199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20973 (p : Pattern) (ha : d8296 p = 1) (hb : d104544 p = 1) : d88206 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8239 q = 1) (hb : d104544 q = 1) : d88147 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8239, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20963 q ha hb
    | true =>
      simp only [d8239, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14694 q ha hb
  have h2 (q : Pattern) (ha : d8285 q = 1) (hb : d104544 q = 1) : d88195 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8285, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8285, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8286 q = 1) (hb : d104544 q = 1) : d88196 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8286, d88196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8286, d88196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8287 q = 1) (hb : d104544 q = 1) : d88197 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8287, d88197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8287, d88197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8288 q = 1) (hb : d104544 q = 1) : d88198 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8288, d88198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8288, d88198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8246 q = 1) (hb : d104544 q = 1) : d88154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8246, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20965 q ha hb
    | true =>
      simp only [d8246, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14696 q ha hb
  have h7 (q : Pattern) (ha : d8292 q = 1) (hb : d104544 q = 1) : d88202 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8292, d88202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8292, d88202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8293 q = 1) (hb : d104544 q = 1) : d88203 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8293, d88203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8293, d88203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8294 q = 1) (hb : d104544 q = 1) : d88204 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8294, d88204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8294, d88204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8295 q = 1) (hb : d104544 q = 1) : d88205 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8295, d88205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8295, d88205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8296 q = 1) (hb : d104544 q = 1) : d88206 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8296, d88206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8296, d88206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro20974 (p : Pattern) (ha : d8363 p = 1) (hb : d104544 p = 1) : d88253 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8239 q = 1) (hb : d104544 q = 1) : d88147 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8239, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20963 q ha hb
    | true =>
      simp only [d8239, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14694 q ha hb
  have h2 (q : Pattern) (ha : d8285 q = 1) (hb : d104544 q = 1) : d88195 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8285, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8285, d88195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8286 q = 1) (hb : d104544 q = 1) : d88196 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8286, d88196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8286, d88196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8287 q = 1) (hb : d104544 q = 1) : d88197 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8287, d88197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8287, d88197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8288 q = 1) (hb : d104544 q = 1) : d88198 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8288, d88198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8288, d88198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14694 q ha hb
    | true =>
      simp only [d43, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d100 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d102 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d103 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8363 q = 1) (hb : d104544 q = 1) : d88253 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8363, d88253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8363, d88253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro20975 (p : Pattern) (ha : d8301 p = 1) (hb : d104544 p = 1) : d88211 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d104544 q = 1) : d88141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20962 q ha hb
    | true =>
      simp only [d6740, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d104544 q = 1) : d88142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14693 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8235 q = 1) (hb : d104544 q = 1) : d88143 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8235, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8236 q = 1) (hb : d104544 q = 1) : d88144 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8236, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8236, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8300 q = 1) (hb : d104544 q = 1) : d88210 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8300, d88210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8300, d88210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8301 q = 1) (hb : d104544 q = 1) : d88211 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8301, d88211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8301, d88211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20976 (p : Pattern) (ha : d8308 p = 1) (hb : d104544 p = 1) : d88218 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d104544 q = 1) : d88141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20962 q ha hb
    | true =>
      simp only [d6740, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d104544 q = 1) : d88142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14693 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8235 q = 1) (hb : d104544 q = 1) : d88143 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8235, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8306 q = 1) (hb : d104544 q = 1) : d88216 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8306, d88216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8306, d88216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8307 q = 1) (hb : d104544 q = 1) : d88217 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8307, d88217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8307, d88217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8308 q = 1) (hb : d104544 q = 1) : d88218 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8308, d88218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8308, d88218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20977 (p : Pattern) (ha : d8313 p = 1) (hb : d104544 p = 1) : d106217 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6797 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d475 q = 1) (hb : d92313 q = 1) : d475 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8312 q = 1) (hb : d104544 q = 1) : d106216 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8312, d104544, d106216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d8312, d104544, d106216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8313 q = 1) (hb : d104544 q = 1) : d106217 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8313, d106217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8313, d106217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro20978 (p : Pattern) (ha : d8319 p = 1) (hb : d104544 p = 1) : d106223 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d104544 q = 1) : d106218 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d106218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20977 q ha hb
    | true =>
      simp only [d8314, d106218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d104544 q = 1) : d106219 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d106219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d106219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6740 q = 1) (hb : d104544 q = 1) : d88141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20962 q ha hb
    | true =>
      simp only [d6740, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6741 q = 1) (hb : d104544 q = 1) : d88142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8316 q = 1) (hb : d104544 q = 1) : d106220 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8316, d106220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8316, d106220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8317 q = 1) (hb : d104544 q = 1) : d106221 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8317, d106221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8317, d106221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8318 q = 1) (hb : d104544 q = 1) : d106222 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8318, d106222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8318, d106222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8319 q = 1) (hb : d104544 q = 1) : d106223 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8319, d106223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8319, d106223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20979 (p : Pattern) (ha : d8334 p = 1) (hb : d104544 p = 1) : d88146 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d104544 q = 1) : d88141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20962 q ha hb
    | true =>
      simp only [d6740, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d104544 q = 1) : d88142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8331 q = 1) (hb : d104544 q = 1) : d88143 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8331, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8331, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8332 q = 1) (hb : d104544 q = 1) : d88144 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8332, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8332, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8333 q = 1) (hb : d104544 q = 1) : d88145 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8333, d88145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8333, d88145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8334 q = 1) (hb : d104544 q = 1) : d88146 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8334, d88146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8334, d88146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20980 (p : Pattern) (ha : d94229 p = 1) (hb : d104544 p = 1) : d106229 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8302 q = 1) (hb : d104544 q = 1) : d88212 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8302, d88212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20975 q ha hb
    | true =>
      simp only [d8302, d88212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14712 q ha hb
  have h2 (q : Pattern) (ha : d8303 q = 1) (hb : d104544 q = 1) : d88213 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8303, d88213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8303, d88213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8304 q = 1) (hb : d104544 q = 1) : d88214 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8304, d88214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8304, d88214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8305 q = 1) (hb : d104544 q = 1) : d88215 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8305, d88215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8305, d88215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8309 q = 1) (hb : d104544 q = 1) : d88219 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8309, d88219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20976 q ha hb
    | true =>
      simp only [d8309, d88219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14713 q ha hb
  have h6 (q : Pattern) (ha : d8310 q = 1) (hb : d104544 q = 1) : d88220 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8310, d88220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8310, d88220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8311 q = 1) (hb : d104544 q = 1) : d88221 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8311, d88221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8311, d88221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8320 q = 1) (hb : d104544 q = 1) : d106224 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8320, d106224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20978 q ha hb
    | true =>
      simp only [d8320, d106224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20963 q ha hb
  have h9 (q : Pattern) (ha : d94225 q = 1) (hb : d104544 q = 1) : d106225 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94225, d106225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94225, d106225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8335 q = 1) (hb : d104544 q = 1) : d88147 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8335, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20979 q ha hb
    | true =>
      simp only [d8335, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8336 q = 1) (hb : d104544 q = 1) : d88148 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8336, d88148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8336, d88148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94226 q = 1) (hb : d104544 q = 1) : d106226 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94226, d106226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94226, d106226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94227 q = 1) (hb : d104544 q = 1) : d106227 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94227, d106227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94227, d106227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94228 q = 1) (hb : d104544 q = 1) : d106228 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94228, d106228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94228, d106228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94229 q = 1) (hb : d104544 q = 1) : d106229 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94229, d106229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94229, d106229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro20981 (p : Pattern) (ha : d8341 p = 1) (hb : d104544 p = 1) : d88236 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d104544 q = 1) : d88141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20962 q ha hb
    | true =>
      simp only [d6740, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d104544 q = 1) : d88142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14693 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8235 q = 1) (hb : d104544 q = 1) : d88143 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8235, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8236 q = 1) (hb : d104544 q = 1) : d88144 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8236, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8236, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8300 q = 1) (hb : d104544 q = 1) : d88210 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8300, d88210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8300, d88210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8341 q = 1) (hb : d104544 q = 1) : d88236 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8341, d88236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8341, d88236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro20982 (p : Pattern) (ha : d8346 p = 1) (hb : d104544 p = 1) : d88241 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d104544 q = 1) : d88141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20962 q ha hb
    | true =>
      simp only [d6740, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d104544 q = 1) : d88142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14693 q ha hb
    | true =>
      simp only [d37, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8235 q = 1) (hb : d104544 q = 1) : d88143 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8235, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8235, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8306 q = 1) (hb : d104544 q = 1) : d88216 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8306, d88216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8306, d88216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8307 q = 1) (hb : d104544 q = 1) : d88217 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8307, d88217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8307, d88217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8346 q = 1) (hb : d104544 q = 1) : d88241 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8346, d88241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8346, d88241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro20983 (p : Pattern) (ha : d8350 p = 1) (hb : d104544 p = 1) : d106230 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d104544 q = 1) : d106218 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d106218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20977 q ha hb
    | true =>
      simp only [d8314, d106218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d104544 q = 1) : d106219 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d106219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d106219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6740 q = 1) (hb : d104544 q = 1) : d88141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20962 q ha hb
    | true =>
      simp only [d6740, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6741 q = 1) (hb : d104544 q = 1) : d88142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8316 q = 1) (hb : d104544 q = 1) : d106220 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8316, d106220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8316, d106220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8317 q = 1) (hb : d104544 q = 1) : d106221 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8317, d106221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8317, d106221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8318 q = 1) (hb : d104544 q = 1) : d106222 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8318, d106222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8318, d106222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8350 q = 1) (hb : d104544 q = 1) : d106230 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8350, d106230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8350, d106230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro20984 (p : Pattern) (ha : d8355 p = 1) (hb : d104544 p = 1) : d88153 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6740 q = 1) (hb : d104544 q = 1) : d88141 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20962 q ha hb
    | true =>
      simp only [d6740, d88141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6741 q = 1) (hb : d104544 q = 1) : d88142 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6741, d88142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8331 q = 1) (hb : d104544 q = 1) : d88143 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8331, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8331, d88143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8332 q = 1) (hb : d104544 q = 1) : d88144 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8332, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8332, d88144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8333 q = 1) (hb : d104544 q = 1) : d88145 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8333, d88145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8333, d88145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8355 q = 1) (hb : d104544 q = 1) : d88153 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8355, d88153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8355, d88153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20985 (p : Pattern) (ha : d94234 p = 1) (hb : d104544 p = 1) : d106236 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8302 q = 1) (hb : d104544 q = 1) : d88212 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8302, d88212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20975 q ha hb
    | true =>
      simp only [d8302, d88212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14712 q ha hb
  have h2 (q : Pattern) (ha : d8303 q = 1) (hb : d104544 q = 1) : d88213 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8303, d88213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8303, d88213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8304 q = 1) (hb : d104544 q = 1) : d88214 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8304, d88214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8304, d88214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8305 q = 1) (hb : d104544 q = 1) : d88215 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8305, d88215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8305, d88215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8309 q = 1) (hb : d104544 q = 1) : d88219 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8309, d88219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20976 q ha hb
    | true =>
      simp only [d8309, d88219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14713 q ha hb
  have h6 (q : Pattern) (ha : d8310 q = 1) (hb : d104544 q = 1) : d88220 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8310, d88220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8310, d88220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8311 q = 1) (hb : d104544 q = 1) : d88221 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8311, d88221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8311, d88221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8320 q = 1) (hb : d104544 q = 1) : d106224 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8320, d106224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20978 q ha hb
    | true =>
      simp only [d8320, d106224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20963 q ha hb
  have h9 (q : Pattern) (ha : d94225 q = 1) (hb : d104544 q = 1) : d106225 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94225, d106225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94225, d106225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8335 q = 1) (hb : d104544 q = 1) : d88147 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8335, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20979 q ha hb
    | true =>
      simp only [d8335, d88147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8336 q = 1) (hb : d104544 q = 1) : d88148 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8336, d88148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d8336, d88148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d94226 q = 1) (hb : d104544 q = 1) : d106226 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94226, d106226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94226, d106226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94227 q = 1) (hb : d104544 q = 1) : d106227 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94227, d106227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d94227, d106227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94228 q = 1) (hb : d104544 q = 1) : d106228 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94228, d106228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94228, d106228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d8342 q = 1) (hb : d104544 q = 1) : d88237 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8342, d88237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20981 q ha hb
    | true =>
      simp only [d8342, d88237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14716 q ha hb
  have h16 (q : Pattern) (ha : d8343 q = 1) (hb : d104544 q = 1) : d88238 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8343, d88238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8343, d88238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d8344 q = 1) (hb : d104544 q = 1) : d88239 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8344, d88239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d8344, d88239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d8345 q = 1) (hb : d104544 q = 1) : d88240 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8345, d88240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8345, d88240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d8347 q = 1) (hb : d104544 q = 1) : d88242 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8347, d88242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20982 q ha hb
    | true =>
      simp only [d8347, d88242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14717 q ha hb
  have h20 (q : Pattern) (ha : d8348 q = 1) (hb : d104544 q = 1) : d88243 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8348, d88243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8348, d88243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d8349 q = 1) (hb : d104544 q = 1) : d88244 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8349, d88244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d8349, d88244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d8351 q = 1) (hb : d104544 q = 1) : d106231 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8351, d106231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20983 q ha hb
    | true =>
      simp only [d8351, d106231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20965 q ha hb
  have h23 (q : Pattern) (ha : d94230 q = 1) (hb : d104544 q = 1) : d106232 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94230, d106232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d94230, d106232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d8356 q = 1) (hb : d104544 q = 1) : d88154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8356, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20984 q ha hb
    | true =>
      simp only [d8356, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d8357 q = 1) (hb : d104544 q = 1) : d88155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8357, d88155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d8357, d88155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d94231 q = 1) (hb : d104544 q = 1) : d106233 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94231, d106233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d94231, d106233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d94232 q = 1) (hb : d104544 q = 1) : d106234 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94232, d106234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94232, d106234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d94233 q = 1) (hb : d104544 q = 1) : d106235 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94233, d106235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d94233, d106235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d94234 q = 1) (hb : d104544 q = 1) : d106236 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94234, d106236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94234, d106236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro20986 (p : Pattern) (ha : d94241 p = 1) (hb : d104544 p = 1) : d106243 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8351 q = 1) (hb : d104544 q = 1) : d106231 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8351, d106231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20983 q ha hb
    | true =>
      simp only [d8351, d106231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20965 q ha hb
  have h2 (q : Pattern) (ha : d94230 q = 1) (hb : d104544 q = 1) : d106232 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94230, d106232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94230, d106232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8356 q = 1) (hb : d104544 q = 1) : d88154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8356, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20984 q ha hb
    | true =>
      simp only [d8356, d88154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8357 q = 1) (hb : d104544 q = 1) : d88155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8357, d88155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8357, d88155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94231 q = 1) (hb : d104544 q = 1) : d106233 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94231, d106233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94231, d106233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94239 q = 1) (hb : d104544 q = 1) : d106241 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94239, d106241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94239, d106241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94240 q = 1) (hb : d104544 q = 1) : d106242 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94240, d106242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94240, d106242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94241 q = 1) (hb : d104544 q = 1) : d106243 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94241, d106243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94241, d106243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20987 (p : Pattern) (ha : d8377 p = 1) (hb : d104544 p = 1) : d106250 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6843 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d673 q = 1) (hb : d92313 q = 1) : d673 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8376 q = 1) (hb : d104544 q = 1) : d106249 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d8376, d104544, d106249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d8376, d104544, d106249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8377 q = 1) (hb : d104544 q = 1) : d106250 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d8377, d106250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8377, d106250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro20988 (p : Pattern) (ha : d8383 p = 1) (hb : d104544 p = 1) : d106256 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8378 q = 1) (hb : d104544 q = 1) : d106251 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8378, d106251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20987 q ha hb
    | true =>
      simp only [d8378, d106251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8379 q = 1) (hb : d104544 q = 1) : d106252 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8379, d106252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8379, d106252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d6773 q = 1) (hb : d104544 q = 1) : d88172 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6773, d88172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20968 q ha hb
    | true =>
      simp only [d6773, d88172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d6774 q = 1) (hb : d104544 q = 1) : d88173 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6774, d88173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6774, d88173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8380 q = 1) (hb : d104544 q = 1) : d106253 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8380, d106253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8380, d106253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8381 q = 1) (hb : d104544 q = 1) : d106254 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8381, d106254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8381, d106254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8382 q = 1) (hb : d104544 q = 1) : d106255 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8382, d106255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8382, d106255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8383 q = 1) (hb : d104544 q = 1) : d106256 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8383, d106256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8383, d106256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro20989 (p : Pattern) (ha : d8398 p = 1) (hb : d104544 p = 1) : d88177 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6773 q = 1) (hb : d104544 q = 1) : d88172 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6773, d88172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20968 q ha hb
    | true =>
      simp only [d6773, d88172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6774 q = 1) (hb : d104544 q = 1) : d88173 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6774, d88173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6774, d88173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8395 q = 1) (hb : d104544 q = 1) : d88174 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8395, d88174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8395, d88174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8396 q = 1) (hb : d104544 q = 1) : d88175 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8396, d88175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8396, d88175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8397 q = 1) (hb : d104544 q = 1) : d88176 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8397, d88176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8397, d88176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8398 q = 1) (hb : d104544 q = 1) : d88177 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8398, d88177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8398, d88177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro20990 (p : Pattern) (ha : d94251 p = 1) (hb : d104544 p = 1) : d106262 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8384 q = 1) (hb : d104544 q = 1) : d106257 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8384, d106257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20988 q ha hb
    | true =>
      simp only [d8384, d106257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20969 q ha hb
  have h2 (q : Pattern) (ha : d94247 q = 1) (hb : d104544 q = 1) : d106258 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94247, d106258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d94247, d106258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8399 q = 1) (hb : d104544 q = 1) : d88178 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8399, d88178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20989 q ha hb
    | true =>
      simp only [d8399, d88178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8400 q = 1) (hb : d104544 q = 1) : d88179 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8400, d88179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8400, d88179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d94248 q = 1) (hb : d104544 q = 1) : d106259 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94248, d106259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d94248, d106259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94249 q = 1) (hb : d104544 q = 1) : d106260 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94249, d106260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94249, d106260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94250 q = 1) (hb : d104544 q = 1) : d106261 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94250, d106261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94250, d106261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94251 q = 1) (hb : d104544 q = 1) : d106262 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94251, d106262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94251, d106262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20991 (p : Pattern) (ha : d94257 p = 1) (hb : d104544 p = 1) : d106268 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8290 q = 1) (hb : d104544 q = 1) : d88200 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8290, d88200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8290, d88200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20972 q ha hb
  have h2 (q : Pattern) (ha : d8291 q = 1) (hb : d104544 q = 1) : d88201 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8291, d88201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8291, d88201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8297 q = 1) (hb : d104544 q = 1) : d88207 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8297, d88207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20972 q ha hb
    | true =>
      simp only [d8297, d88207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20973 q ha hb
  have h4 (q : Pattern) (ha : d8298 q = 1) (hb : d104544 q = 1) : d88208 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8298, d88208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8298, d88208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8299 q = 1) (hb : d104544 q = 1) : d88209 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8299, d88209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8299, d88209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d94235 q = 1) (hb : d104544 q = 1) : d106237 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94235, d106237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20980 q ha hb
    | true =>
      simp only [d94235, d106237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20985 q ha hb
  have h7 (q : Pattern) (ha : d8364 q = 1) (hb : d104544 q = 1) : d88254 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8364, d88254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20974 q ha hb
    | true =>
      simp only [d8364, d88254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14704 q ha hb
  have h8 (q : Pattern) (ha : d94236 q = 1) (hb : d104544 q = 1) : d106238 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94236, d106238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d94236, d106238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94237 q = 1) (hb : d104544 q = 1) : d106239 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94237, d106239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d94237, d106239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d94238 q = 1) (hb : d104544 q = 1) : d106240 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94238, d106240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d94238, d106240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d94242 q = 1) (hb : d104544 q = 1) : d106244 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94242, d106244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94242, d106244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20986 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14723 q ha hb
  have h13 (q : Pattern) (ha : d94243 q = 1) (hb : d104544 q = 1) : d106245 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94243, d106245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d94243, d106245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94244 q = 1) (hb : d104544 q = 1) : d106246 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94244, d106246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d94244, d106246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d94245 q = 1) (hb : d104544 q = 1) : d106247 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94245, d106247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d94245, d106247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d94246 q = 1) (hb : d104544 q = 1) : d106248 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94246, d106248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d94246, d106248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d94252 q = 1) (hb : d104544 q = 1) : d106263 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94252, d106263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94252, d106263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20990 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14724 q ha hb
  have h19 (q : Pattern) (ha : d94253 q = 1) (hb : d104544 q = 1) : d106264 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94253, d106264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d94253, d106264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d94254 q = 1) (hb : d104544 q = 1) : d106265 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94254, d106265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d94254, d106265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d94255 q = 1) (hb : d104544 q = 1) : d106266 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94255, d106266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d94255, d106266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d94256 q = 1) (hb : d104544 q = 1) : d106267 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94256, d106267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d94256, d106267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d94257 q = 1) (hb : d104544 q = 1) : d106268 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94257, d106268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d94257, d106268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro20992 (p : Pattern) (ha : d94263 p = 1) (hb : d104544 p = 1) : d106274 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14702 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d94220 q = 1) (hb : d104544 q = 1) : d88190 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94220, d88190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94220, d88190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20971 q ha hb
  have h6 (q : Pattern) (ha : d94221 q = 1) (hb : d104544 q = 1) : d88191 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94221, d88191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94221, d88191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d94222 q = 1) (hb : d104544 q = 1) : d88192 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94222, d88192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94222, d88192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d94223 q = 1) (hb : d104544 q = 1) : d88193 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94223, d88193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94223, d88193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d94224 q = 1) (hb : d104544 q = 1) : d88194 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94224, d88194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d94224, d88194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d94258 q = 1) (hb : d104544 q = 1) : d106269 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94258, d106269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94258, d106269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20991 q ha hb
  have h11 (q : Pattern) (ha : d94259 q = 1) (hb : d104544 q = 1) : d106270 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94259, d106270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94259, d106270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d94260 q = 1) (hb : d104544 q = 1) : d106271 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94260, d106271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94260, d106271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d94261 q = 1) (hb : d104544 q = 1) : d106272 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94261, d106272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94261, d106272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d94262 q = 1) (hb : d104544 q = 1) : d106273 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94262, d106273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d94262, d106273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d94263 q = 1) (hb : d104544 q = 1) : d106274 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94263, d106274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d94263, d106274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro20993 (p : Pattern) (ha : d8420 p = 1) (hb : d104544 p = 1) : d106278 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d104544 q = 1) : d106218 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d106218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20977 q ha hb
    | true =>
      simp only [d8314, d106218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d104544 q = 1) : d106219 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d106219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d106219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14744 q ha hb
    | true =>
      simp only [d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8417 q = 1) (hb : d104544 q = 1) : d106275 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8417, d106275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8417, d106275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8418 q = 1) (hb : d104544 q = 1) : d106276 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8418, d106276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8418, d106276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8419 q = 1) (hb : d104544 q = 1) : d106277 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8419, d106277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8419, d106277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8420 q = 1) (hb : d104544 q = 1) : d106278 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8420, d106278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8420, d106278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20994 (p : Pattern) (ha : d8426 p = 1) (hb : d104544 p = 1) : d106284 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8421 q = 1) (hb : d104544 q = 1) : d106279 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8421, d106279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20993 q ha hb
    | true =>
      simp only [d8421, d106279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14746 q ha hb
  have h2 (q : Pattern) (ha : d8422 q = 1) (hb : d104544 q = 1) : d106280 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8422, d106280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8422, d106280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8423 q = 1) (hb : d104544 q = 1) : d106281 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8423, d106281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8423, d106281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8424 q = 1) (hb : d104544 q = 1) : d106282 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8424, d106282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8424, d106282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8425 q = 1) (hb : d104544 q = 1) : d106283 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8425, d106283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8425, d106283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8426 q = 1) (hb : d104544 q = 1) : d106284 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8426, d106284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8426, d106284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro20995 (p : Pattern) (ha : d8429 p = 1) (hb : d104544 p = 1) : d106287 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8314 q = 1) (hb : d104544 q = 1) : d106218 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8314, d106218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20977 q ha hb
    | true =>
      simp only [d8314, d106218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d8315 q = 1) (hb : d104544 q = 1) : d106219 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8315, d106219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8315, d106219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14744 q ha hb
    | true =>
      simp only [d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8417 q = 1) (hb : d104544 q = 1) : d106275 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8417, d106275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8417, d106275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8418 q = 1) (hb : d104544 q = 1) : d106276 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8418, d106276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8418, d106276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8419 q = 1) (hb : d104544 q = 1) : d106277 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8419, d106277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8419, d106277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8429 q = 1) (hb : d104544 q = 1) : d106287 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8429, d106287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8429, d106287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro20996 (p : Pattern) (ha : d8435 p = 1) (hb : d104544 p = 1) : d106293 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8421 q = 1) (hb : d104544 q = 1) : d106279 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8421, d106279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20993 q ha hb
    | true =>
      simp only [d8421, d106279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14746 q ha hb
  have h2 (q : Pattern) (ha : d8422 q = 1) (hb : d104544 q = 1) : d106280 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8422, d106280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8422, d106280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8423 q = 1) (hb : d104544 q = 1) : d106281 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8423, d106281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8423, d106281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8424 q = 1) (hb : d104544 q = 1) : d106282 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8424, d106282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8424, d106282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8425 q = 1) (hb : d104544 q = 1) : d106283 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8425, d106283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8425, d106283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8430 q = 1) (hb : d104544 q = 1) : d106288 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8430, d106288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20995 q ha hb
    | true =>
      simp only [d8430, d106288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14749 q ha hb
  have h7 (q : Pattern) (ha : d8431 q = 1) (hb : d104544 q = 1) : d106289 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8431, d106289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8431, d106289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8432 q = 1) (hb : d104544 q = 1) : d106290 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8432, d106290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d8432, d106290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d8433 q = 1) (hb : d104544 q = 1) : d106291 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8433, d106291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8433, d106291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8434 q = 1) (hb : d104544 q = 1) : d106292 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8434, d106292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8434, d106292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8435 q = 1) (hb : d104544 q = 1) : d106293 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8435, d106293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8435, d106293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro20997 (p : Pattern) (ha : d6799 p = 1) (hb : d104544 p = 1) : d121858 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d6797 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4822 q = 1) (hb : d92313 q = 1) : d4822 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6798 q = 1) (hb : d104544 q = 1) : d121857 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d6798, d104544, d121857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d6798, d104544, d121857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d6799 q = 1) (hb : d104544 q = 1) : d121858 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d6799, d121858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d6799, d121858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro20998 (p : Pattern) (ha : d8463 p = 1) (hb : d104544 p = 1) : d121868 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d6800 q = 1) (hb : d104544 q = 1) : d121859 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6800, d121859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20997 q ha hb
    | true =>
      simp only [d6800, d121859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d6801 q = 1) (hb : d104544 q = 1) : d121860 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6801, d121860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6801, d121860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14744 q ha hb
    | true =>
      simp only [d482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8460 q = 1) (hb : d104544 q = 1) : d121865 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8460, d121865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8460, d121865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8461 q = 1) (hb : d104544 q = 1) : d121866 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8461, d121866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8461, d121866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d8462 q = 1) (hb : d104544 q = 1) : d121867 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8462, d121867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8462, d121867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d8463 q = 1) (hb : d104544 q = 1) : d121868 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8463, d121868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8463, d121868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro20999 (p : Pattern) (ha : d8514 p = 1) (hb : d104544 p = 1) : d121889 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8509 q = 1) (hb : d104544 q = 1) : d121884 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8509, d121884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20998 q ha hb
    | true =>
      simp only [d8509, d121884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14746 q ha hb
  have h2 (q : Pattern) (ha : d8510 q = 1) (hb : d104544 q = 1) : d121885 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8510, d121885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8510, d121885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8511 q = 1) (hb : d104544 q = 1) : d121886 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8511, d121886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8511, d121886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d8512 q = 1) (hb : d104544 q = 1) : d121887 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8512, d121887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8512, d121887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8513 q = 1) (hb : d104544 q = 1) : d121888 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8513, d121888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8513, d121888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d633 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14746 q ha hb
    | true =>
      simp only [d633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d634 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d635 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d636 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d637 q = 1) (hb : d104544 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d8514 q = 1) (hb : d104544 q = 1) : d121889 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8514, d121889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8514, d121889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
end NetHack.Soko22Hazard87
