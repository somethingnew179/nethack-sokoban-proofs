import NetHack.Soko22Hazard87.EqIntroBlocks0007
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro2000 (p : Pattern) (selected : d2782 p = 2) : d54509 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2777 q = 2) : d54504 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d2777, d54504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1999 q selected
    | true =>
      simp only [d2777, d54504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2778 q = 2) : d54505 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d2778, d54505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2778, d54505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2779 q = 2) : d54506 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d2779, d54506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2779, d54506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2780 q = 2) : d54507 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d2780, d54507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2780, d54507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2781 q = 2) : d54508 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d2781, d54508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2781, d54508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2782 q = 2) : d54509 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d2782, d54509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2782, d54509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2001 (p : Pattern) (selected : d61811 p = 0) : d61922 p = 1 := by
  have h0 (q : Pattern) (selected : d56 q = 0) : d51908 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56, d51908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro191 q selected
    | true =>
      simp only [d56, d51908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro193 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d57 q = 0) : d51909 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57, d51909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d57, d51909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d58 q = 0) : d51910 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58, d51910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d58, d51910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d61811 q = 0) : d61922 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61811, d61922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d61811, d61922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h4 p selected
theorem eqIntro2002 (p : Pattern) (selected : d61816 p = 0) : d61927 p = 1 := by
  have h0 (q : Pattern) (selected : d212 q = 0) : d52030 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212, d52030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro214 q selected
    | true =>
      simp only [d212, d52030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro219 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d214 q = 0) : d52032 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro220 q selected
    | true =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d215 q = 0) : d52033 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d215, d52033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d215, d52033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d216 q = 0) : d52034 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d216, d52034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d216, d52034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d61816 q = 0) : d61927 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61816, d61927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d61816, d61927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h5 p selected
theorem eqIntro2003 (p : Pattern) (selected : d61822 p = 0) : d61933 p = 1 := by
  have h0 (q : Pattern) (selected : d396 q = 0) : d52162 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d396, d52162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro244 q selected
    | true =>
      simp only [d396, d52162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro249 q selected
  have h1 (q : Pattern) (selected : d398 q = 0) : d52164 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d398, d52164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro250 q selected
    | true =>
      simp only [d398, d52164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro201 q selected
  have h2 (q : Pattern) (selected : d399 q = 0) : d52165 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d399, d52165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d399, d52165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h4 (q : Pattern) (selected : d400 q = 0) : d52166 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d400, d52166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d400, d52166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d61822 q = 0) : d61933 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61822, d61933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d61822, d61933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h5 p selected
theorem eqIntro2004 (p : Pattern) (selected : d61828 p = 0) : d61939 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d61812 q = 0) : d61923 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61812, d61923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61812, d61923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2001 q selected
  have h2 (q : Pattern) (selected : d61813 q = 0) : d61924 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61813, d61924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61813, d61924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d61814 q = 0) : d61925 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61814, d61925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61814, d61925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d61815 q = 0) : d61926 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61815, d61926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61815, d61926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d61817 q = 0) : d61928 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61817, d61928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61817, d61928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2002 q selected
  have h6 (q : Pattern) (selected : d61818 q = 0) : d61929 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61818, d61929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61818, d61929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d61819 q = 0) : d61930 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61819, d61930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61819, d61930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d61820 q = 0) : d61931 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61820, d61931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61820, d61931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d61821 q = 0) : d61932 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61821, d61932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d61821, d61932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d61823 q = 0) : d61934 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61823, d61934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61823, d61934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2003 q selected
  have h11 (q : Pattern) (selected : d61824 q = 0) : d61935 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61824, d61935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61824, d61935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d61825 q = 0) : d61936 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61825, d61936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61825, d61936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d61826 q = 0) : d61937 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61826, d61937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61826, d61937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d61827 q = 0) : d61938 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61827, d61938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61827, d61938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d61828 q = 0) : d61939 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61828, d61939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d61828, d61939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro2005 (p : Pattern) (selected : d61829 p = 0) : d61940 p = 1 := by
  have h0 (q : Pattern) (selected : d632 q = 0) : d52336 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d632, d52336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro288 q selected
    | true =>
      simp only [d632, d52336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro296 q selected
  have h1 (q : Pattern) (selected : d645 q = 0) : d52349 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d645, d52349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro297 q selected
    | true =>
      simp only [d645, d52349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro298 q selected
  have h2 (q : Pattern) (selected : d646 q = 0) : d52350 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d646, d52350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d646, d52350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h4 (q : Pattern) (selected : d647 q = 0) : d52351 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d647, d52351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d647, d52351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d61829 q = 0) : d61940 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61829, d61940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d61829, d61940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h5 p selected
theorem eqIntro2006 (p : Pattern) (selected : d61835 p = 0) : d61946 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d61830 q = 0) : d61941 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61830, d61941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61830, d61941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2005 q selected
  have h2 (q : Pattern) (selected : d61831 q = 0) : d61942 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61831, d61942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61831, d61942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d61832 q = 0) : d61943 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61832, d61943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61832, d61943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d61833 q = 0) : d61944 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61833, d61944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61833, d61944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d61834 q = 0) : d61945 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61834, d61945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61834, d61945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d61835 q = 0) : d61946 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61835, d61946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61835, d61946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2007 (p : Pattern) (selected : d61837 p = 0) : d61948 p = 1 := by
  have h0 (q : Pattern) (selected : d938 q = 0) : d52557 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d938, d52557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro350 q selected
    | true =>
      simp only [d938, d52557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro358 q selected
  have h1 (q : Pattern) (selected : d951 q = 0) : d52570 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d951, d52570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro359 q selected
    | true =>
      simp only [d951, d52570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro360 q selected
  have h2 (q : Pattern) (selected : d952 q = 0) : d52571 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d952, d52571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d952, d52571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h4 (q : Pattern) (selected : d953 q = 0) : d52572 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d953, d52572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d953, d52572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d61837 q = 0) : d61948 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61837, d61948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d61837, d61948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h5 p selected
theorem eqIntro2008 (p : Pattern) (selected : d61843 p = 0) : d61954 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d61838 q = 0) : d61949 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61838, d61949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61838, d61949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2007 q selected
  have h2 (q : Pattern) (selected : d61839 q = 0) : d61950 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61839, d61950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61839, d61950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d61840 q = 0) : d61951 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61840, d61951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61840, d61951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d61841 q = 0) : d61952 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61841, d61952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61841, d61952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d61842 q = 0) : d61953 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61842, d61953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61842, d61953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d61843 q = 0) : d61954 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61843, d61954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61843, d61954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2009 (p : Pattern) (selected : d61846 p = 0) : d61957 p = 1 := by
  have h0 (q : Pattern) (selected : d1349 q = 0) : d52837 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1349, d52837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro426 q selected
    | true =>
      simp only [d1349, d52837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro434 q selected
  have h1 (q : Pattern) (selected : d1362 q = 0) : d52850 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1362, d52850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro435 q selected
    | true =>
      simp only [d1362, d52850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro436 q selected
  have h2 (q : Pattern) (selected : d1363 q = 0) : d52851 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1363, d52851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1363, d52851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h4 (q : Pattern) (selected : d1364 q = 0) : d52852 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1364, d52852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1364, d52852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d61846 q = 0) : d61957 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61846, d61957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d61846, d61957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h5 p selected
theorem eqIntro2010 (p : Pattern) (selected : d61852 p = 0) : d61963 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d61847 q = 0) : d61958 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61847, d61958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61847, d61958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2009 q selected
  have h2 (q : Pattern) (selected : d61848 q = 0) : d61959 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61848, d61959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61848, d61959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d61849 q = 0) : d61960 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61849, d61960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61849, d61960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d61850 q = 0) : d61961 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61850, d61961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61850, d61961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d61851 q = 0) : d61962 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61851, d61962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61851, d61962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d61852 q = 0) : d61963 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61852, d61963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61852, d61963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2011 (p : Pattern) (selected : d61856 p = 0) : d61967 p = 1 := by
  have h0 (q : Pattern) (selected : d1826 q = 0) : d53152 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1826, d53152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro512 q selected
    | true =>
      simp only [d1826, d53152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro520 q selected
  have h1 (q : Pattern) (selected : d1839 q = 0) : d53165 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1839, d53165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro521 q selected
    | true =>
      simp only [d1839, d53165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro522 q selected
  have h2 (q : Pattern) (selected : d1840 q = 0) : d53166 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1840, d53166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1840, d53166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h4 (q : Pattern) (selected : d1841 q = 0) : d53167 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1841, d53167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1841, d53167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d61856 q = 0) : d61967 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61856, d61967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d61856, d61967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h5 p selected
theorem eqIntro2012 (p : Pattern) (selected : d61862 p = 0) : d61973 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d61857 q = 0) : d61968 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61857, d61968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61857, d61968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2011 q selected
  have h2 (q : Pattern) (selected : d61858 q = 0) : d61969 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61858, d61969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61858, d61969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d61859 q = 0) : d61970 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61859, d61970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61859, d61970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d61860 q = 0) : d61971 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61860, d61971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61860, d61971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d61861 q = 0) : d61972 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61861, d61972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61861, d61972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d61862 q = 0) : d61973 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61862, d61973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61862, d61973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2013 (p : Pattern) (selected : d61867 p = 0) : d61978 p = 1 := by
  have h0 (q : Pattern) (selected : d2304 q = 0) : d53469 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2304, d53469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro602 q selected
    | true =>
      simp only [d2304, d53469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro610 q selected
  have h1 (q : Pattern) (selected : d2317 q = 0) : d53482 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2317, d53482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro611 q selected
    | true =>
      simp only [d2317, d53482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro612 q selected
  have h2 (q : Pattern) (selected : d2318 q = 0) : d53483 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2318, d53483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2318, d53483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h4 (q : Pattern) (selected : d2319 q = 0) : d53484 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2319, d53484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2319, d53484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d61867 q = 0) : d61978 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61867, d61978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d61867, d61978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h5 p selected
theorem eqIntro2014 (p : Pattern) (selected : d61873 p = 0) : d61984 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d61868 q = 0) : d61979 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61868, d61979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61868, d61979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2013 q selected
  have h2 (q : Pattern) (selected : d61869 q = 0) : d61980 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61869, d61980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61869, d61980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d61870 q = 0) : d61981 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61870, d61981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61870, d61981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d61871 q = 0) : d61982 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61871, d61982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61871, d61982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d61872 q = 0) : d61983 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61872, d61983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61872, d61983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d61873 q = 0) : d61984 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61873, d61984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61873, d61984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2015 (p : Pattern) (selected : d61879 p = 0) : d61990 p = 1 := by
  have h0 (q : Pattern) (selected : d61836 q = 0) : d61947 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61836, d61947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2004 q selected
    | true =>
      simp only [d61836, d61947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2006 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d61844 q = 0) : d61955 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61844, d61955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61844, d61955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2008 q selected
  have h3 (q : Pattern) (selected : d61845 q = 0) : d61956 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61845, d61956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61845, d61956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d61853 q = 0) : d61964 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61853, d61964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61853, d61964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2010 q selected
  have h5 (q : Pattern) (selected : d61854 q = 0) : d61965 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61854, d61965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61854, d61965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d61855 q = 0) : d61966 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61855, d61966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d61855, d61966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d61863 q = 0) : d61974 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61863, d61974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61863, d61974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2012 q selected
  have h8 (q : Pattern) (selected : d61864 q = 0) : d61975 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61864, d61975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61864, d61975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d61865 q = 0) : d61976 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61865, d61976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61865, d61976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d61866 q = 0) : d61977 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d61866, d61977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d61866, d61977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d61874 q = 0) : d61985 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61874, d61985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61874, d61985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2014 q selected
  have h12 (q : Pattern) (selected : d61875 q = 0) : d61986 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61875, d61986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61875, d61986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d61876 q = 0) : d61987 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61876, d61987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61876, d61987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d61877 q = 0) : d61988 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d61877, d61988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61877, d61988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d61878 q = 0) : d61989 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d61878, d61989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d61878, d61989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d61879 q = 0) : d61990 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d61879, d61990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d61879, d61990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro2016 (p : Pattern) (selected : d61885 p = 0) : d61996 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d61880 q = 0) : d61991 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d61880, d61991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2015 q selected
    | true =>
      simp only [d61880, d61991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d61881 q = 0) : d61992 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d61881, d61992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61881, d61992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d61882 q = 0) : d61993 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d61882, d61993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d61882, d61993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d61883 q = 0) : d61994 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d61883, d61994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d61883, d61994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d61884 q = 0) : d61995 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d61884, d61995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d61884, d61995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d61885 q = 0) : d61996 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d61885, d61996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d61885, d61996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2017 (p : Pattern) (selected : d61891 p = 0) : d62002 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d61886 q = 0) : d61997 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d61886, d61997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2016 q selected
    | true =>
      simp only [d61886, d61997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d61887 q = 0) : d61998 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d61887, d61998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61887, d61998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d61888 q = 0) : d61999 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d61888, d61999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d61888, d61999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d61889 q = 0) : d62000 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d61889, d62000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d61889, d62000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d61890 q = 0) : d62001 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d61890, d62001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d61890, d62001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d61891 q = 0) : d62002 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d61891, d62002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d61891, d62002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2018 (p : Pattern) (selected : d61897 p = 0) : d62008 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d61892 q = 0) : d62003 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d61892, d62003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2017 q selected
    | true =>
      simp only [d61892, d62003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d61893 q = 0) : d62004 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d61893, d62004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61893, d62004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d61894 q = 0) : d62005 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d61894, d62005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d61894, d62005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d61895 q = 0) : d62006 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d61895, d62006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d61895, d62006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d61896 q = 0) : d62007 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d61896, d62007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d61896, d62007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d61897 q = 0) : d62008 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d61897, d62008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d61897, d62008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2019 (p : Pattern) (selected : d61903 p = 0) : d62014 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d61898 q = 0) : d62009 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d61898, d62009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2018 q selected
    | true =>
      simp only [d61898, d62009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d61899 q = 0) : d62010 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d61899, d62010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61899, d62010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d61900 q = 0) : d62011 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d61900, d62011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d61900, d62011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d61901 q = 0) : d62012 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d61901, d62012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d61901, d62012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d61902 q = 0) : d62013 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d61902, d62013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d61902, d62013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d61903 q = 0) : d62014 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d61903, d62014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d61903, d62014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2020 (p : Pattern) (selected : d61909 p = 0) : d62020 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d61904 q = 0) : d62015 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d61904, d62015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2019 q selected
    | true =>
      simp only [d61904, d62015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d61905 q = 0) : d62016 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d61905, d62016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61905, d62016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d61906 q = 0) : d62017 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d61906, d62017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d61906, d62017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d61907 q = 0) : d62018 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d61907, d62018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d61907, d62018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d61908 q = 0) : d62019 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d61908, d62019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d61908, d62019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d61909 q = 0) : d62020 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d61909, d62020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d61909, d62020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2021 (p : Pattern) (selected : d61915 p = 0) : d62026 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d61910 q = 0) : d62021 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d61910, d62021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2020 q selected
    | true =>
      simp only [d61910, d62021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d61911 q = 0) : d62022 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d61911, d62022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61911, d62022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d61912 q = 0) : d62023 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d61912, d62023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d61912, d62023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d61913 q = 0) : d62024 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d61913, d62024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d61913, d62024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d61914 q = 0) : d62025 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d61914, d62025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d61914, d62025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d61915 q = 0) : d62026 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d61915, d62026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d61915, d62026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2022 (p : Pattern) (selected : d61921 p = 0) : d62032 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d61916 q = 0) : d62027 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d61916, d62027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2021 q selected
    | true =>
      simp only [d61916, d62027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d61917 q = 0) : d62028 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d61917, d62028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61917, d62028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d61918 q = 0) : d62029 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d61918, d62029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d61918, d62029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d61919 q = 0) : d62030 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d61919, d62030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d61919, d62030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d61920 q = 0) : d62031 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d61920, d62031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d61920, d62031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d61921 q = 0) : d62032 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d61921, d62032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d61921, d62032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2023 (p : Pattern) (selected : d61816 p = 1) : d62265 p = 1 := by
  have h0 (q : Pattern) (selected : d212 q = 1) : d51647 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212, d51647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5 q selected
    | true =>
      simp only [d212, d51647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7 q selected
  have h1 (q : Pattern) (selected : d214 q = 1) : d214 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d215 q = 1) : d51648 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d215, d51648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d215, d51648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d216 q = 1) : d51649 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d216, d51649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d216, d51649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d61816 q = 1) : d62265 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61816, d62265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d61816, d62265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h5 p selected
theorem eqIntro2024 (p : Pattern) (selected : d61822 p = 1) : d62271 p = 1 := by
  have h0 (q : Pattern) (selected : d396 q = 1) : d51664 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d396, d51664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19 q selected
    | true =>
      simp only [d396, d51664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21 q selected
  have h1 (q : Pattern) (selected : d398 q = 1) : d398 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d399 q = 1) : d51665 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d399, d51665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d399, d51665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d400 q = 1) : d51666 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d400, d51666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d400, d51666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d61822 q = 1) : d62271 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61822, d62271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d61822, d62271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h5 p selected
theorem eqIntro2025 (p : Pattern) (selected : d61828 p = 1) : d62277 p = 1 := by
  have h0 (q : Pattern) (selected : d61815 q = 1) : d61815 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d61817 q = 1) : d62266 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61817, d62266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61817, d62266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2023 q selected
  have h3 (q : Pattern) (selected : d61818 q = 1) : d62267 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61818, d62267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61818, d62267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d61819 q = 1) : d62268 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61819, d62268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61819, d62268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d61820 q = 1) : d62269 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61820, d62269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61820, d62269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d61821 q = 1) : d62270 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61821, d62270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61821, d62270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d61823 q = 1) : d62272 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61823, d62272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61823, d62272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2024 q selected
  have h8 (q : Pattern) (selected : d61824 q = 1) : d62273 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61824, d62273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61824, d62273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d61825 q = 1) : d62274 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61825, d62274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61825, d62274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d61826 q = 1) : d62275 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61826, d62275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61826, d62275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d61827 q = 1) : d62276 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61827, d62276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61827, d62276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d61828 q = 1) : d62277 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61828, d62277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d61828, d62277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro2026 (p : Pattern) (selected : d61829 p = 1) : d62278 p = 1 := by
  have h0 (q : Pattern) (selected : d632 q = 1) : d51689 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d632, d51689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36 q selected
    | true =>
      simp only [d632, d51689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39 q selected
  have h1 (q : Pattern) (selected : d645 q = 1) : d645 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d646 q = 1) : d51690 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d646, d51690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d646, d51690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d647 q = 1) : d51691 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d647, d51691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d647, d51691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d61829 q = 1) : d62278 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61829, d62278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d61829, d62278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h5 p selected
theorem eqIntro2027 (p : Pattern) (selected : d61835 p = 1) : d62284 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d61830 q = 1) : d62279 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61830, d62279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61830, d62279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2026 q selected
  have h2 (q : Pattern) (selected : d61831 q = 1) : d62280 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61831, d62280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61831, d62280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d61832 q = 1) : d62281 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61832, d62281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61832, d62281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d61833 q = 1) : d62282 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61833, d62282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61833, d62282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d61834 q = 1) : d62283 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61834, d62283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61834, d62283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d61835 q = 1) : d62284 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61835, d62284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61835, d62284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2028 (p : Pattern) (selected : d61837 p = 1) : d62286 p = 1 := by
  have h0 (q : Pattern) (selected : d938 q = 1) : d51715 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d938, d51715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro60 q selected
    | true =>
      simp only [d938, d51715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro63 q selected
  have h1 (q : Pattern) (selected : d951 q = 1) : d951 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d952 q = 1) : d51716 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d952, d51716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d952, d51716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d953 q = 1) : d51717 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d953, d51717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d953, d51717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d61837 q = 1) : d62286 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61837, d62286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d61837, d62286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h5 p selected
theorem eqIntro2029 (p : Pattern) (selected : d61843 p = 1) : d62292 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d61838 q = 1) : d62287 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61838, d62287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61838, d62287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2028 q selected
  have h2 (q : Pattern) (selected : d61839 q = 1) : d62288 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61839, d62288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61839, d62288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d61840 q = 1) : d62289 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61840, d62289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61840, d62289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d61841 q = 1) : d62290 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61841, d62290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61841, d62290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d61842 q = 1) : d62291 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61842, d62291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61842, d62291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d61843 q = 1) : d62292 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61843, d62292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61843, d62292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2030 (p : Pattern) (selected : d61846 p = 1) : d62295 p = 1 := by
  have h0 (q : Pattern) (selected : d1349 q = 1) : d51742 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1349, d51742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro90 q selected
    | true =>
      simp only [d1349, d51742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro93 q selected
  have h1 (q : Pattern) (selected : d1362 q = 1) : d1362 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1363 q = 1) : d51743 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1363, d51743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1363, d51743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d1364 q = 1) : d51744 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1364, d51744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1364, d51744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d61846 q = 1) : d62295 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61846, d62295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d61846, d62295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h5 p selected
theorem eqIntro2031 (p : Pattern) (selected : d61852 p = 1) : d62301 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d61847 q = 1) : d62296 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61847, d62296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61847, d62296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2030 q selected
  have h2 (q : Pattern) (selected : d61848 q = 1) : d62297 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61848, d62297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61848, d62297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d61849 q = 1) : d62298 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61849, d62298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61849, d62298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d61850 q = 1) : d62299 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61850, d62299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61850, d62299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d61851 q = 1) : d62300 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61851, d62300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61851, d62300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d61852 q = 1) : d62301 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61852, d62301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61852, d62301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2032 (p : Pattern) (selected : d61856 p = 1) : d62305 p = 1 := by
  have h0 (q : Pattern) (selected : d1826 q = 1) : d51770 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1826, d51770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro126 q selected
    | true =>
      simp only [d1826, d51770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro129 q selected
  have h1 (q : Pattern) (selected : d1839 q = 1) : d1839 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1840 q = 1) : d51771 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1840, d51771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1840, d51771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d1841 q = 1) : d51772 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1841, d51772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1841, d51772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d61856 q = 1) : d62305 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61856, d62305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d61856, d62305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h5 p selected
theorem eqIntro2033 (p : Pattern) (selected : d61862 p = 1) : d62311 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d61857 q = 1) : d62306 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61857, d62306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61857, d62306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2032 q selected
  have h2 (q : Pattern) (selected : d61858 q = 1) : d62307 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61858, d62307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61858, d62307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d61859 q = 1) : d62308 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61859, d62308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61859, d62308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d61860 q = 1) : d62309 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61860, d62309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61860, d62309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d61861 q = 1) : d62310 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61861, d62310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61861, d62310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d61862 q = 1) : d62311 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61862, d62311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61862, d62311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2034 (p : Pattern) (selected : d61867 p = 1) : d62316 p = 1 := by
  have h0 (q : Pattern) (selected : d2304 q = 1) : d51799 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2304, d51799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro163 q selected
    | true =>
      simp only [d2304, d51799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro166 q selected
  have h1 (q : Pattern) (selected : d2317 q = 1) : d2317 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d2318 q = 1) : d51800 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2318, d51800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2318, d51800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d2319 q = 1) : d51801 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2319, d51801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2319, d51801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d61867 q = 1) : d62316 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d61867, d62316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d61867, d62316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h5 p selected
theorem eqIntro2035 (p : Pattern) (selected : d61873 p = 1) : d62322 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d61868 q = 1) : d62317 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d61868, d62317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61868, d62317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2034 q selected
  have h2 (q : Pattern) (selected : d61869 q = 1) : d62318 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d61869, d62318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61869, d62318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d61870 q = 1) : d62319 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d61870, d62319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61870, d62319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d61871 q = 1) : d62320 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d61871, d62320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61871, d62320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d61872 q = 1) : d62321 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d61872, d62321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61872, d62321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d61873 q = 1) : d62322 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d61873, d62322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61873, d62322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2036 (p : Pattern) (selected : d61879 p = 1) : d62328 p = 1 := by
  have h0 (q : Pattern) (selected : d61836 q = 1) : d62285 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61836, d62285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2025 q selected
    | true =>
      simp only [d61836, d62285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2027 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d61844 q = 1) : d62293 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61844, d62293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61844, d62293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2029 q selected
  have h3 (q : Pattern) (selected : d61845 q = 1) : d62294 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61845, d62294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61845, d62294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d61853 q = 1) : d62302 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61853, d62302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61853, d62302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2031 q selected
  have h5 (q : Pattern) (selected : d61854 q = 1) : d62303 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61854, d62303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61854, d62303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d61855 q = 1) : d62304 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61855, d62304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d61855, d62304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d61863 q = 1) : d62312 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61863, d62312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61863, d62312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2033 q selected
  have h8 (q : Pattern) (selected : d61864 q = 1) : d62313 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61864, d62313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61864, d62313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d61865 q = 1) : d62314 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61865, d62314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61865, d62314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d61866 q = 1) : d62315 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d61866, d62315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d61866, d62315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d61874 q = 1) : d62323 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d61874, d62323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61874, d62323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2035 q selected
  have h12 (q : Pattern) (selected : d61875 q = 1) : d62324 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d61875, d62324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61875, d62324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d61876 q = 1) : d62325 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d61876, d62325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61876, d62325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d61877 q = 1) : d62326 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d61877, d62326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61877, d62326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d61878 q = 1) : d62327 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d61878, d62327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d61878, d62327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d61879 q = 1) : d62328 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d61879, d62328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d61879, d62328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro2037 (p : Pattern) (selected : d61885 p = 1) : d62334 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d61880 q = 1) : d62329 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d61880, d62329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2036 q selected
    | true =>
      simp only [d61880, d62329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d61881 q = 1) : d62330 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d61881, d62330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61881, d62330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d61882 q = 1) : d62331 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d61882, d62331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d61882, d62331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d61883 q = 1) : d62332 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d61883, d62332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d61883, d62332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d61884 q = 1) : d62333 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d61884, d62333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d61884, d62333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d61885 q = 1) : d62334 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d61885, d62334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d61885, d62334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2038 (p : Pattern) (selected : d61891 p = 1) : d62340 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d61886 q = 1) : d62335 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d61886, d62335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2037 q selected
    | true =>
      simp only [d61886, d62335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d61887 q = 1) : d62336 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d61887, d62336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61887, d62336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d61888 q = 1) : d62337 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d61888, d62337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d61888, d62337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d61889 q = 1) : d62338 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d61889, d62338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d61889, d62338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d61890 q = 1) : d62339 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d61890, d62339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d61890, d62339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d61891 q = 1) : d62340 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d61891, d62340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d61891, d62340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2039 (p : Pattern) (selected : d61897 p = 1) : d62346 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d61892 q = 1) : d62341 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d61892, d62341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2038 q selected
    | true =>
      simp only [d61892, d62341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d61893 q = 1) : d62342 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d61893, d62342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61893, d62342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d61894 q = 1) : d62343 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d61894, d62343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d61894, d62343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d61895 q = 1) : d62344 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d61895, d62344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d61895, d62344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d61896 q = 1) : d62345 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d61896, d62345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d61896, d62345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d61897 q = 1) : d62346 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d61897, d62346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d61897, d62346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2040 (p : Pattern) (selected : d61903 p = 1) : d62352 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d61898 q = 1) : d62347 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d61898, d62347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2039 q selected
    | true =>
      simp only [d61898, d62347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d61899 q = 1) : d62348 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d61899, d62348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61899, d62348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d61900 q = 1) : d62349 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d61900, d62349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d61900, d62349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d61901 q = 1) : d62350 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d61901, d62350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d61901, d62350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d61902 q = 1) : d62351 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d61902, d62351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d61902, d62351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d61903 q = 1) : d62352 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d61903, d62352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d61903, d62352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2041 (p : Pattern) (selected : d61909 p = 1) : d62358 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d61904 q = 1) : d62353 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d61904, d62353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2040 q selected
    | true =>
      simp only [d61904, d62353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d61905 q = 1) : d62354 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d61905, d62354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61905, d62354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d61906 q = 1) : d62355 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d61906, d62355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d61906, d62355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d61907 q = 1) : d62356 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d61907, d62356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d61907, d62356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d61908 q = 1) : d62357 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d61908, d62357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d61908, d62357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d61909 q = 1) : d62358 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d61909, d62358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d61909, d62358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2042 (p : Pattern) (selected : d61915 p = 1) : d62364 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d61910 q = 1) : d62359 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d61910, d62359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2041 q selected
    | true =>
      simp only [d61910, d62359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d61911 q = 1) : d62360 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d61911, d62360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61911, d62360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d61912 q = 1) : d62361 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d61912, d62361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d61912, d62361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d61913 q = 1) : d62362 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d61913, d62362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d61913, d62362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d61914 q = 1) : d62363 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d61914, d62363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d61914, d62363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d61915 q = 1) : d62364 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d61915, d62364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d61915, d62364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2043 (p : Pattern) (selected : d61921 p = 1) : d62370 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d61916 q = 1) : d62365 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d61916, d62365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2042 q selected
    | true =>
      simp only [d61916, d62365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d61917 q = 1) : d62366 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d61917, d62366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d61917, d62366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d61918 q = 1) : d62367 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d61918, d62367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d61918, d62367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d61919 q = 1) : d62368 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d61919, d62368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d61919, d62368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d61920 q = 1) : d62369 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d61920, d62369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d61920, d62369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d61921 q = 1) : d62370 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d61921, d62370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d61921, d62370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2044 (p : Pattern) (selected : d3497 p = 0) : d62377 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d43 q = 0) : d51895 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44 q = 0) : d51896 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44, d51896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d45 q = 0) : d51897 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d45, d51897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d45, d51897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d46 q = 0) : d51898 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d46, d51898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d46, d51898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d47 q = 0) : d51899 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d47, d51899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d47, d51899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3497 q = 0) : d62377 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3497, d62377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3497, d62377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2045 (p : Pattern) (selected : d3503 p = 0) : d62383 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3498 q = 0) : d62378 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3498, d62378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3498, d62378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2044 q selected
  have h2 (q : Pattern) (selected : d3499 q = 0) : d62379 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3499, d62379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3499, d62379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3500 q = 0) : d62380 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3500, d62380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3500, d62380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3501 q = 0) : d62381 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3501, d62381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3501, d62381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3502 q = 0) : d62382 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3502, d62382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3502, d62382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3503 q = 0) : d62383 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3503, d62383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3503, d62383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2046 (p : Pattern) (selected : d3509 p = 0) : d62389 p = 1 := by
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
  have h8 (q : Pattern) (selected : d157 q = 0) : d52008 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro208 q selected
    | true =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
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
  have h10 (q : Pattern) (selected : d189 q = 0) : d52009 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189, d52009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d189, d52009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
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
  have h13 (q : Pattern) (selected : d190 q = 0) : d52010 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d190, d52010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d190, d52010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d191 q = 0) : d52011 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d191, d52011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d191, d52011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d192 q = 0) : d52012 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d192, d52012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d192, d52012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d3509 q = 0) : d62389 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3509, d62389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d3509, d62389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro2047 (p : Pattern) (selected : d3515 p = 0) : d62395 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2525 q = 0) : d55598 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2525, d55598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2525, d55598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro220 q selected
  have h2 (q : Pattern) (selected : d2526 q = 0) : d55599 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2526, d55599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2526, d55599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3508 q = 0) : d62388 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3508, d62388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3508, d62388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3510 q = 0) : d62390 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3510, d62390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3510, d62390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2046 q selected
  have h5 (q : Pattern) (selected : d214 q = 0) : d52032 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro220 q selected
    | true =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3511 q = 0) : d62391 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3511, d62391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3511, d62391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3512 q = 0) : d62392 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3512, d62392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3512, d62392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3513 q = 0) : d62393 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3513, d62393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3513, d62393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3514 q = 0) : d62394 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3514, d62394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d3514, d62394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d3515 q = 0) : d62395 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3515, d62395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3515, d62395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro2048 (p : Pattern) (selected : d3522 p = 0) : d62402 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d297 q = 0) : d52096 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d52096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro232 q selected
    | true =>
      simp only [d297, d52096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro202 q selected
  have h2 (q : Pattern) (selected : d298 q = 0) : d52097 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d52097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d298, d52097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d299 q = 0) : d52098 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d52098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d299, d52098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d300 q = 0) : d52099 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d52099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d300, d52099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d304 q = 0) : d52103 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d52103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro233 q selected
    | true =>
      simp only [d304, d52103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro203 q selected
  have h6 (q : Pattern) (selected : d305 q = 0) : d52104 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d52104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d305, d52104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d306 q = 0) : d52105 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d52105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d306, d52105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d337 q = 0) : d52136 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d337, d52136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro238 q selected
    | true =>
      simp only [d337, d52136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro208 q selected
  have h9 (q : Pattern) (selected : d368 q = 0) : d52008 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368, d52008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro243 q selected
    | true =>
      simp only [d368, d52008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro213 q selected
  have h10 (q : Pattern) (selected : d369 q = 0) : d52137 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d369, d52137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d369, d52137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d370 q = 0) : d52138 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d370, d52138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro208 q selected
    | true =>
      simp only [d370, d52138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d371 q = 0) : d52139 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d371, d52139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d371, d52139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d372 q = 0) : d52140 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d372, d52140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d372, d52140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d373 q = 0) : d52141 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d373, d52141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d373, d52141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d374 q = 0) : d52142 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d374, d52142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d374, d52142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d3522 q = 0) : d62402 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3522, d62402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d3522, d62402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro2049 (p : Pattern) (selected : d3529 p = 0) : d62409 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2537 q = 0) : d55610 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2537, d55610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2537, d55610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1357 q selected
  have h2 (q : Pattern) (selected : d2538 q = 0) : d55611 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2538, d55611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2538, d55611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3521 q = 0) : d62401 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3521, d62401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3521, d62401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3523 q = 0) : d62403 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3523, d62403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3523, d62403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2048 q selected
  have h5 (q : Pattern) (selected : d3524 q = 0) : d62404 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3524, d62404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1357 q selected
    | true =>
      simp only [d3524, d62404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro220 q selected
  have h6 (q : Pattern) (selected : d3525 q = 0) : d62405 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3525, d62405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3525, d62405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3526 q = 0) : d62406 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3526, d62406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3526, d62406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3527 q = 0) : d62407 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3527, d62407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3527, d62407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3528 q = 0) : d62408 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3528, d62408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d3528, d62408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d3529 q = 0) : d62409 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3529, d62409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3529, d62409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro2050 (p : Pattern) (selected : d3535 p = 0) : d62415 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3504 q = 0) : d62384 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3504, d62384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3504, d62384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2045 q selected
  have h2 (q : Pattern) (selected : d3505 q = 0) : d62385 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3505, d62385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3505, d62385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3506 q = 0) : d62386 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3506, d62386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3506, d62386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3507 q = 0) : d62387 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3507, d62387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3507, d62387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3516 q = 0) : d62396 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3516, d62396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3516, d62396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2047 q selected
  have h6 (q : Pattern) (selected : d3517 q = 0) : d62397 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3517, d62397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3517, d62397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3518 q = 0) : d62398 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3518, d62398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3518, d62398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d3519 q = 0) : d62399 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3519, d62399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3519, d62399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3520 q = 0) : d62400 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3520, d62400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3520, d62400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d3530 q = 0) : d62410 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3530, d62410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3530, d62410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2049 q selected
  have h11 (q : Pattern) (selected : d3531 q = 0) : d62411 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3531, d62411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3531, d62411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d3532 q = 0) : d62412 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3532, d62412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3532, d62412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d3533 q = 0) : d62413 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3533, d62413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3533, d62413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d3534 q = 0) : d62414 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3534, d62414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3534, d62414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d3535 q = 0) : d62415 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3535, d62415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3535, d62415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro2051 (p : Pattern) (selected : d3537 p = 0) : d62417 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d515 q = 0) : d52262 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d515, d52262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro271 q selected
    | true =>
      simp only [d515, d52262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro272 q selected
  have h2 (q : Pattern) (selected : d516 q = 0) : d52263 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d516, d52263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d516, d52263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d517 q = 0) : d52264 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d517, d52264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d517, d52264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d518 q = 0) : d52265 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d518, d52265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d518, d52265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d525 q = 0) : d52272 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d525, d52272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro273 q selected
    | true =>
      simp only [d525, d52272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro274 q selected
  have h6 (q : Pattern) (selected : d526 q = 0) : d52273 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d526, d52273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d526, d52273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d527 q = 0) : d52274 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d527, d52274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d527, d52274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d561 q = 0) : d52308 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d561, d52308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro280 q selected
    | true =>
      simp only [d561, d52308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro265 q selected
  have h9 (q : Pattern) (selected : d601 q = 0) : d52239 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d601, d52239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro286 q selected
    | true =>
      simp only [d601, d52239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro287 q selected
  have h10 (q : Pattern) (selected : d602 q = 0) : d52309 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d602, d52309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d602, d52309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d603 q = 0) : d52310 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d603, d52310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro265 q selected
    | true =>
      simp only [d603, d52310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d604 q = 0) : d52311 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d604, d52311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d604, d52311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d605 q = 0) : d52312 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d605, d52312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d605, d52312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d606 q = 0) : d52313 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d606, d52313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d606, d52313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d607 q = 0) : d52314 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d607, d52314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d607, d52314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d3537 q = 0) : d62417 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3537, d62417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d3537, d62417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro2052 (p : Pattern) (selected : d3539 p = 0) : d62419 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d633 q = 0) : d52337 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d52337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro266 q selected
    | true =>
      simp only [d633, d52337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d634 q = 0) : d52338 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d52338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d634, d52338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d635 q = 0) : d52339 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d52339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d635, d52339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d636 q = 0) : d52340 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d52340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d636, d52340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d637 q = 0) : d52341 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d52341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d637, d52341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3539 q = 0) : d62419 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3539, d62419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3539, d62419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2053 (p : Pattern) (selected : d3545 p = 0) : d62425 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2550 q = 0) : d55623 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2550, d55623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2550, d55623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1360 q selected
  have h2 (q : Pattern) (selected : d2551 q = 0) : d55624 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2551, d55624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2551, d55624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3536 q = 0) : d62416 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3536, d62416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3536, d62416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3538 q = 0) : d62418 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3538, d62418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3538, d62418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2051 q selected
  have h5 (q : Pattern) (selected : d3540 q = 0) : d62420 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3540, d62420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1360 q selected
    | true =>
      simp only [d3540, d62420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2052 q selected
  have h6 (q : Pattern) (selected : d3541 q = 0) : d62421 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3541, d62421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3541, d62421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3542 q = 0) : d62422 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3542, d62422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3542, d62422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3543 q = 0) : d62423 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3543, d62423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3543, d62423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3544 q = 0) : d62424 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3544, d62424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d3544, d62424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d3545 q = 0) : d62425 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3545, d62425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3545, d62425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro2054 (p : Pattern) (selected : d3551 p = 0) : d62431 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3546 q = 0) : d62426 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3546, d62426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3546, d62426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2053 q selected
  have h2 (q : Pattern) (selected : d3547 q = 0) : d62427 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3547, d62427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3547, d62427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3548 q = 0) : d62428 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3548, d62428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3548, d62428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3549 q = 0) : d62429 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3549, d62429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3549, d62429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3550 q = 0) : d62430 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3550, d62430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3550, d62430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3551 q = 0) : d62431 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3551, d62431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3551, d62431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2055 (p : Pattern) (selected : d3554 p = 0) : d62434 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d807 q = 0) : d52484 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d807, d52484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro329 q selected
    | true =>
      simp only [d807, d52484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro330 q selected
  have h2 (q : Pattern) (selected : d808 q = 0) : d52485 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d808, d52485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d808, d52485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d809 q = 0) : d52486 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d809, d52486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d809, d52486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d810 q = 0) : d52487 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d810, d52487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d810, d52487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d817 q = 0) : d52494 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d817, d52494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro331 q selected
    | true =>
      simp only [d817, d52494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro332 q selected
  have h6 (q : Pattern) (selected : d818 q = 0) : d52495 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d818, d52495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d818, d52495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d819 q = 0) : d52496 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d819, d52496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d819, d52496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d852 q = 0) : d52529 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d852, d52529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro338 q selected
    | true =>
      simp only [d852, d52529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro323 q selected
  have h9 (q : Pattern) (selected : d907 q = 0) : d52461 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d907, d52461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro348 q selected
    | true =>
      simp only [d907, d52461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro349 q selected
  have h10 (q : Pattern) (selected : d908 q = 0) : d52530 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d908, d52530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d908, d52530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d909 q = 0) : d52531 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d909, d52531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro323 q selected
    | true =>
      simp only [d909, d52531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d910 q = 0) : d52532 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d910, d52532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d910, d52532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d911 q = 0) : d52533 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d911, d52533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d911, d52533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d912 q = 0) : d52534 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d912, d52534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d912, d52534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d913 q = 0) : d52535 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d913, d52535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d913, d52535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d3554 q = 0) : d62434 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3554, d62434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d3554, d62434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro2056 (p : Pattern) (selected : d3556 p = 0) : d62436 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d939 q = 0) : d52558 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d52558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro324 q selected
    | true =>
      simp only [d939, d52558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d940 q = 0) : d52559 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d52559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d940, d52559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d941 q = 0) : d52560 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d52560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d941, d52560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d942 q = 0) : d52561 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d52561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d942, d52561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d943 q = 0) : d52562 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d52562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d943, d52562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3556 q = 0) : d62436 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3556, d62436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3556, d62436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2057 (p : Pattern) (selected : d3562 p = 0) : d62442 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2564 q = 0) : d55637 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2564, d55637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2564, d55637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1363 q selected
  have h2 (q : Pattern) (selected : d2565 q = 0) : d55638 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2565, d55638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2565, d55638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3553 q = 0) : d62433 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3553, d62433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3553, d62433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3555 q = 0) : d62435 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3555, d62435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3555, d62435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2055 q selected
  have h5 (q : Pattern) (selected : d3557 q = 0) : d62437 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3557, d62437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1363 q selected
    | true =>
      simp only [d3557, d62437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2056 q selected
  have h6 (q : Pattern) (selected : d3558 q = 0) : d62438 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3558, d62438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3558, d62438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3559 q = 0) : d62439 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3559, d62439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3559, d62439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3560 q = 0) : d62440 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3560, d62440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3560, d62440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3561 q = 0) : d62441 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3561, d62441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d3561, d62441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d3562 q = 0) : d62442 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3562, d62442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3562, d62442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro2058 (p : Pattern) (selected : d3568 p = 0) : d62448 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3563 q = 0) : d62443 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3563, d62443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3563, d62443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2057 q selected
  have h2 (q : Pattern) (selected : d3564 q = 0) : d62444 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3564, d62444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3564, d62444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3565 q = 0) : d62445 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3565, d62445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3565, d62445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3566 q = 0) : d62446 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3566, d62446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3566, d62446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3567 q = 0) : d62447 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3567, d62447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3567, d62447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3568 q = 0) : d62448 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3568, d62448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3568, d62448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2059 (p : Pattern) (selected : d3572 p = 0) : d62452 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1186 q = 0) : d52767 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1186, d52767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro401 q selected
    | true =>
      simp only [d1186, d52767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro402 q selected
  have h2 (q : Pattern) (selected : d1187 q = 0) : d52768 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1187, d52768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1187, d52768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1188 q = 0) : d52769 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, d52769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1188, d52769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1189 q = 0) : d52770 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, d52770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1189, d52770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1196 q = 0) : d52777 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1196, d52777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro403 q selected
    | true =>
      simp only [d1196, d52777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro404 q selected
  have h6 (q : Pattern) (selected : d1197 q = 0) : d52778 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1197, d52778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1197, d52778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1198 q = 0) : d52779 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, d52779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1198, d52779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d1228 q = 0) : d52809 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1228, d52809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro410 q selected
    | true =>
      simp only [d1228, d52809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro395 q selected
  have h9 (q : Pattern) (selected : d1318 q = 0) : d52744 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1318, d52744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro424 q selected
    | true =>
      simp only [d1318, d52744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro425 q selected
  have h10 (q : Pattern) (selected : d1319 q = 0) : d52810 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1319, d52810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1319, d52810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d1320 q = 0) : d52811 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1320, d52811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro395 q selected
    | true =>
      simp only [d1320, d52811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d1321 q = 0) : d52812 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1321, d52812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d1321, d52812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d1322 q = 0) : d52813 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1322, d52813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d1322, d52813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d1323 q = 0) : d52814 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1323, d52814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1323, d52814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d1324 q = 0) : d52815 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1324, d52815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1324, d52815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d3572 q = 0) : d62452 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3572, d62452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d3572, d62452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro2060 (p : Pattern) (selected : d3574 p = 0) : d62454 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1350 q = 0) : d52838 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, d52838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro396 q selected
    | true =>
      simp only [d1350, d52838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1351 q = 0) : d52839 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, d52839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1351, d52839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1352 q = 0) : d52840 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, d52840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1352, d52840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1353 q = 0) : d52841 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, d52841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1353, d52841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1354 q = 0) : d52842 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, d52842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1354, d52842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3574 q = 0) : d62454 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3574, d62454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3574, d62454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2061 (p : Pattern) (selected : d3580 p = 0) : d62460 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2579 q = 0) : d55652 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2579, d55652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2579, d55652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1366 q selected
  have h2 (q : Pattern) (selected : d2580 q = 0) : d55653 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2580, d55653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2580, d55653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3571 q = 0) : d62451 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3571, d62451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3571, d62451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3573 q = 0) : d62453 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3573, d62453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3573, d62453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2059 q selected
  have h5 (q : Pattern) (selected : d3575 q = 0) : d62455 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3575, d62455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1366 q selected
    | true =>
      simp only [d3575, d62455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2060 q selected
  have h6 (q : Pattern) (selected : d3576 q = 0) : d62456 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3576, d62456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3576, d62456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3577 q = 0) : d62457 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3577, d62457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3577, d62457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3578 q = 0) : d62458 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3578, d62458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3578, d62458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3579 q = 0) : d62459 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3579, d62459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d3579, d62459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d3580 q = 0) : d62460 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3580, d62460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3580, d62460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro2062 (p : Pattern) (selected : d3586 p = 0) : d62466 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3581 q = 0) : d62461 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3581, d62461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3581, d62461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2061 q selected
  have h2 (q : Pattern) (selected : d3582 q = 0) : d62462 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3582, d62462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3582, d62462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3583 q = 0) : d62463 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3583, d62463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3583, d62463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3584 q = 0) : d62464 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3584, d62464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3584, d62464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3585 q = 0) : d62465 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3585, d62465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3585, d62465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3586 q = 0) : d62466 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3586, d62466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3586, d62466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2063 (p : Pattern) (selected : d3591 p = 0) : d62471 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1647 q = 0) : d53088 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1647, d53088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro483 q selected
    | true =>
      simp only [d1647, d53088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro484 q selected
  have h2 (q : Pattern) (selected : d1648 q = 0) : d53089 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1648, d53089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1648, d53089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1649 q = 0) : d53090 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, d53090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1649, d53090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1650 q = 0) : d53091 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, d53091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1650, d53091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1657 q = 0) : d53098 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1657, d53098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro485 q selected
    | true =>
      simp only [d1657, d53098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro486 q selected
  have h6 (q : Pattern) (selected : d1658 q = 0) : d53099 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1658, d53099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1658, d53099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1659 q = 0) : d53100 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, d53100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1659, d53100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d1683 q = 0) : d53124 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1683, d53124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro490 q selected
    | true =>
      simp only [d1683, d53124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro477 q selected
  have h9 (q : Pattern) (selected : d1795 q = 0) : d53065 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1795, d53065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro510 q selected
    | true =>
      simp only [d1795, d53065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro511 q selected
  have h10 (q : Pattern) (selected : d1796 q = 0) : d53125 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1796, d53125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1796, d53125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d1797 q = 0) : d53126 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1797, d53126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro477 q selected
    | true =>
      simp only [d1797, d53126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d1798 q = 0) : d53127 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1798, d53127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d1798, d53127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d1799 q = 0) : d53128 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1799, d53128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d1799, d53128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d1800 q = 0) : d53129 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1800, d53129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1800, d53129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d1801 q = 0) : d53130 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1801, d53130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1801, d53130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d3591 q = 0) : d62471 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3591, d62471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d3591, d62471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro2064 (p : Pattern) (selected : d3593 p = 0) : d62473 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1827 q = 0) : d53153 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, d53153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro478 q selected
    | true =>
      simp only [d1827, d53153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1828 q = 0) : d53154 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, d53154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1828, d53154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1829 q = 0) : d53155 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, d53155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1829, d53155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1830 q = 0) : d53156 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, d53156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1830, d53156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1831 q = 0) : d53157 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, d53157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1831, d53157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3593 q = 0) : d62473 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3593, d62473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3593, d62473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2065 (p : Pattern) (selected : d3599 p = 0) : d62479 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2595 q = 0) : d55668 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2595, d55668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2595, d55668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1369 q selected
  have h2 (q : Pattern) (selected : d2596 q = 0) : d55669 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2596, d55669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2596, d55669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3590 q = 0) : d62470 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3590, d62470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3590, d62470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3592 q = 0) : d62472 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3592, d62472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3592, d62472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2063 q selected
  have h5 (q : Pattern) (selected : d3594 q = 0) : d62474 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3594, d62474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1369 q selected
    | true =>
      simp only [d3594, d62474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2064 q selected
  have h6 (q : Pattern) (selected : d3595 q = 0) : d62475 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3595, d62475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3595, d62475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3596 q = 0) : d62476 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3596, d62476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3596, d62476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3597 q = 0) : d62477 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3597, d62477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3597, d62477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3598 q = 0) : d62478 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3598, d62478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d3598, d62478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d3599 q = 0) : d62479 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3599, d62479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3599, d62479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro2066 (p : Pattern) (selected : d3605 p = 0) : d62485 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3600 q = 0) : d62480 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3600, d62480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3600, d62480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2065 q selected
  have h2 (q : Pattern) (selected : d3601 q = 0) : d62481 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3601, d62481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3601, d62481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3602 q = 0) : d62482 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3602, d62482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3602, d62482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3603 q = 0) : d62483 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3603, d62483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3603, d62483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3604 q = 0) : d62484 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3604, d62484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3604, d62484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3605 q = 0) : d62485 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3605, d62485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3605, d62485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2067 (p : Pattern) (selected : d3611 p = 0) : d62491 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2130 q = 0) : d53409 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2130, d53409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro572 q selected
    | true =>
      simp only [d2130, d53409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro573 q selected
  have h2 (q : Pattern) (selected : d2131 q = 0) : d53410 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2131, d53410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2131, d53410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2132 q = 0) : d53411 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, d53411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2132, d53411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2133 q = 0) : d53412 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, d53412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2133, d53412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2140 q = 0) : d53419 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2140, d53419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro574 q selected
    | true =>
      simp only [d2140, d53419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro575 q selected
  have h6 (q : Pattern) (selected : d2141 q = 0) : d53420 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2141, d53420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2141, d53420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2142 q = 0) : d53421 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, d53421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2142, d53421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d2162 q = 0) : d53441 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2162, d53441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro579 q selected
    | true =>
      simp only [d2162, d53441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro566 q selected
  have h9 (q : Pattern) (selected : d2273 q = 0) : d53386 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2273, d53386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro600 q selected
    | true =>
      simp only [d2273, d53386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro601 q selected
  have h10 (q : Pattern) (selected : d2274 q = 0) : d53442 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2274, d53442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d2274, d53442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d2275 q = 0) : d53443 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2275, d53443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro566 q selected
    | true =>
      simp only [d2275, d53443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d2276 q = 0) : d53444 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2276, d53444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d2276, d53444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d2277 q = 0) : d53445 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2277, d53445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d2277, d53445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d2278 q = 0) : d53446 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2278, d53446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d2278, d53446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d2279 q = 0) : d53447 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2279, d53447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2279, d53447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d3611 q = 0) : d62491 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3611, d62491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d3611, d62491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro2068 (p : Pattern) (selected : d3613 p = 0) : d62493 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2305 q = 0) : d53470 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, d53470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro567 q selected
    | true =>
      simp only [d2305, d53470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2306 q = 0) : d53471 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, d53471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2306, d53471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2307 q = 0) : d53472 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, d53472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2307, d53472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2308 q = 0) : d53473 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, d53473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2308, d53473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2309 q = 0) : d53474 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, d53474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2309, d53474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3613 q = 0) : d62493 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3613, d62493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3613, d62493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2069 (p : Pattern) (selected : d3619 p = 0) : d62499 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2612 q = 0) : d55685 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2612, d55685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2612, d55685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1372 q selected
  have h2 (q : Pattern) (selected : d2613 q = 0) : d55686 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2613, d55686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2613, d55686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3610 q = 0) : d62490 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3610, d62490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3610, d62490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3612 q = 0) : d62492 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3612, d62492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3612, d62492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2067 q selected
  have h5 (q : Pattern) (selected : d3614 q = 0) : d62494 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3614, d62494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1372 q selected
    | true =>
      simp only [d3614, d62494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2068 q selected
  have h6 (q : Pattern) (selected : d3615 q = 0) : d62495 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3615, d62495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3615, d62495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3616 q = 0) : d62496 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3616, d62496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3616, d62496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3617 q = 0) : d62497 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3617, d62497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3617, d62497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3618 q = 0) : d62498 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3618, d62498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d3618, d62498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d3619 q = 0) : d62499 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3619, d62499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3619, d62499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro2070 (p : Pattern) (selected : d3625 p = 0) : d62505 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3620 q = 0) : d62500 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3620, d62500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3620, d62500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2069 q selected
  have h2 (q : Pattern) (selected : d3621 q = 0) : d62501 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3621, d62501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3621, d62501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3622 q = 0) : d62502 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3622, d62502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3622, d62502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3623 q = 0) : d62503 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3623, d62503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3623, d62503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3624 q = 0) : d62504 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3624, d62504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3624, d62504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3625 q = 0) : d62505 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3625, d62505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3625, d62505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2071 (p : Pattern) (selected : d3631 p = 0) : d62511 p = 1 := by
  have h0 (q : Pattern) (selected : d3552 q = 0) : d62432 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3552, d62432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2050 q selected
    | true =>
      simp only [d3552, d62432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2054 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d3569 q = 0) : d62449 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3569, d62449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3569, d62449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2058 q selected
  have h3 (q : Pattern) (selected : d3570 q = 0) : d62450 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3570, d62450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3570, d62450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3587 q = 0) : d62467 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3587, d62467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3587, d62467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2062 q selected
  have h5 (q : Pattern) (selected : d3588 q = 0) : d62468 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3588, d62468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3588, d62468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3589 q = 0) : d62469 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3589, d62469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3589, d62469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3606 q = 0) : d62486 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3606, d62486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3606, d62486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2066 q selected
  have h8 (q : Pattern) (selected : d3607 q = 0) : d62487 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3607, d62487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3607, d62487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3608 q = 0) : d62488 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3608, d62488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3608, d62488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d3609 q = 0) : d62489 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d3609, d62489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3609, d62489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d3626 q = 0) : d62506 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3626, d62506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3626, d62506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2070 q selected
  have h12 (q : Pattern) (selected : d3627 q = 0) : d62507 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3627, d62507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3627, d62507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d3628 q = 0) : d62508 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3628, d62508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3628, d62508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d3629 q = 0) : d62509 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d3629, d62509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3629, d62509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d3630 q = 0) : d62510 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d3630, d62510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d3630, d62510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d3631 q = 0) : d62511 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d3631, d62511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d3631, d62511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro2072 (p : Pattern) (selected : d3637 p = 0) : d62517 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3632 q = 0) : d62512 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d3632, d62512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2071 q selected
    | true =>
      simp only [d3632, d62512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3633 q = 0) : d62513 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d3633, d62513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3633, d62513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3634 q = 0) : d62514 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d3634, d62514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3634, d62514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3635 q = 0) : d62515 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d3635, d62515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3635, d62515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3636 q = 0) : d62516 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d3636, d62516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3636, d62516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3637 q = 0) : d62517 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d3637, d62517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3637, d62517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2073 (p : Pattern) (selected : d3643 p = 0) : d62523 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3638 q = 0) : d62518 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d3638, d62518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2072 q selected
    | true =>
      simp only [d3638, d62518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3639 q = 0) : d62519 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d3639, d62519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3639, d62519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3640 q = 0) : d62520 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d3640, d62520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3640, d62520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3641 q = 0) : d62521 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d3641, d62521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3641, d62521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3642 q = 0) : d62522 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d3642, d62522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3642, d62522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3643 q = 0) : d62523 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d3643, d62523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3643, d62523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2074 (p : Pattern) (selected : d3649 p = 0) : d62529 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3644 q = 0) : d62524 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d3644, d62524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2073 q selected
    | true =>
      simp only [d3644, d62524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3645 q = 0) : d62525 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d3645, d62525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3645, d62525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3646 q = 0) : d62526 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d3646, d62526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3646, d62526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3647 q = 0) : d62527 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d3647, d62527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3647, d62527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3648 q = 0) : d62528 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d3648, d62528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3648, d62528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3649 q = 0) : d62529 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d3649, d62529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3649, d62529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2075 (p : Pattern) (selected : d3655 p = 0) : d62535 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3650 q = 0) : d62530 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d3650, d62530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2074 q selected
    | true =>
      simp only [d3650, d62530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3651 q = 0) : d62531 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d3651, d62531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3651, d62531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3652 q = 0) : d62532 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d3652, d62532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3652, d62532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3653 q = 0) : d62533 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d3653, d62533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3653, d62533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3654 q = 0) : d62534 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d3654, d62534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3654, d62534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3655 q = 0) : d62535 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d3655, d62535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3655, d62535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2076 (p : Pattern) (selected : d3661 p = 0) : d62541 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3656 q = 0) : d62536 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d3656, d62536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2075 q selected
    | true =>
      simp only [d3656, d62536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3657 q = 0) : d62537 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d3657, d62537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3657, d62537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3658 q = 0) : d62538 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d3658, d62538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3658, d62538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3659 q = 0) : d62539 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d3659, d62539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3659, d62539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3660 q = 0) : d62540 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d3660, d62540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3660, d62540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3661 q = 0) : d62541 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d3661, d62541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3661, d62541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2077 (p : Pattern) (selected : d3667 p = 0) : d62547 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3662 q = 0) : d62542 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d3662, d62542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2076 q selected
    | true =>
      simp only [d3662, d62542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3663 q = 0) : d62543 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d3663, d62543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3663, d62543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3664 q = 0) : d62544 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d3664, d62544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3664, d62544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3665 q = 0) : d62545 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d3665, d62545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3665, d62545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3666 q = 0) : d62546 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d3666, d62546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3666, d62546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3667 q = 0) : d62547 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d3667, d62547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3667, d62547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2078 (p : Pattern) (selected : d3673 p = 0) : d62553 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3668 q = 0) : d62548 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d3668, d62548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2077 q selected
    | true =>
      simp only [d3668, d62548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3669 q = 0) : d62549 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d3669, d62549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3669, d62549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3670 q = 0) : d62550 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d3670, d62550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3670, d62550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3671 q = 0) : d62551 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d3671, d62551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3671, d62551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3672 q = 0) : d62552 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d3672, d62552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3672, d62552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3673 q = 0) : d62553 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d3673, d62553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3673, d62553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2079 (p : Pattern) (selected : d3509 p = 1) : d62554 p = 1 := by
  have h0 (q : Pattern) (selected : d120 q = 1) : d120 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d126 q = 1) : d126 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d157 q = 1) : d157 q = 1 := by
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
  have h5 (q : Pattern) (selected : d189 q = 1) : d4335 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d189, d4335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d189, d4335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44 q = 1) : d44 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d190 q = 1) : d4336 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d190, d4336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d190, d4336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d191 q = 1) : d51641 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d191, d51641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d191, d51641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d192 q = 1) : d51642 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d192, d51642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d192, d51642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d3509 q = 1) : d62554 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3509, d62554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3509, d62554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  exact h10 p selected
theorem eqIntro2080 (p : Pattern) (selected : d3515 p = 1) : d62560 p = 1 := by
  have h0 (q : Pattern) (selected : d3508 q = 1) : d3508 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d3510 q = 1) : d62555 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3510, d62555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3510, d62555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2079 q selected
  have h3 (q : Pattern) (selected : d214 q = 1) : d214 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d3511 q = 1) : d62556 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3511, d62556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3511, d62556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3512 q = 1) : d62557 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3512, d62557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3512, d62557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d3513 q = 1) : d62558 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3513, d62558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3513, d62558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3514 q = 1) : d62559 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3514, d62559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3514, d62559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d3515 q = 1) : d62560 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3515, d62560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d3515, d62560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h8 p selected
theorem eqIntro2081 (p : Pattern) (selected : d3522 p = 1) : d62566 p = 1 := by
  have h0 (q : Pattern) (selected : d300 q = 1) : d300 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d306 q = 1) : d306 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d337 q = 1) : d337 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d368 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro18 q selected
    | true =>
      simp only [d368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4 q selected
  have h4 (q : Pattern) (selected : d369 q = 1) : d4371 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d369, d4371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d369, d4371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d371 q = 1) : d371 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d372 q = 1) : d4372 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d372, d4372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d372, d4372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d373 q = 1) : d51658 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d373, d51658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d373, d51658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d374 q = 1) : d51659 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d374, d51659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d374, d51659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d3522 q = 1) : d62566 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3522, d62566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d3522, d62566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro2082 (p : Pattern) (selected : d3529 p = 1) : d62572 p = 1 := by
  have h0 (q : Pattern) (selected : d3521 q = 1) : d3521 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d3523 q = 1) : d62567 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3523, d62567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3523, d62567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2081 q selected
  have h3 (q : Pattern) (selected : d3524 q = 1) : d3524 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d3525 q = 1) : d62568 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3525, d62568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3525, d62568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3526 q = 1) : d62569 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3526, d62569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3526, d62569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d3527 q = 1) : d62570 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3527, d62570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3527, d62570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3528 q = 1) : d62571 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3528, d62571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3528, d62571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d3529 q = 1) : d62572 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3529, d62572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d3529, d62572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h8 p selected
theorem eqIntro2083 (p : Pattern) (selected : d3535 p = 1) : d62578 p = 1 := by
  have h0 (q : Pattern) (selected : d3507 q = 1) : d3507 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d3516 q = 1) : d62561 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3516, d62561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3516, d62561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2080 q selected
  have h3 (q : Pattern) (selected : d3517 q = 1) : d62562 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3517, d62562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3517, d62562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3518 q = 1) : d62563 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3518, d62563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3518, d62563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3519 q = 1) : d62564 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3519, d62564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3519, d62564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3520 q = 1) : d62565 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3520, d62565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3520, d62565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3530 q = 1) : d62573 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3530, d62573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3530, d62573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2082 q selected
  have h8 (q : Pattern) (selected : d3531 q = 1) : d62574 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3531, d62574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3531, d62574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3532 q = 1) : d62575 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3532, d62575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3532, d62575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d3533 q = 1) : d62576 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3533, d62576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3533, d62576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d3534 q = 1) : d62577 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3534, d62577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3534, d62577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d3535 q = 1) : d62578 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3535, d62578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3535, d62578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro2084 (p : Pattern) (selected : d3537 p = 1) : d62579 p = 1 := by
  have h0 (q : Pattern) (selected : d518 q = 1) : d518 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d527 q = 1) : d527 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d561 q = 1) : d561 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d601 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro34 q selected
    | true =>
      simp only [d601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35 q selected
  have h4 (q : Pattern) (selected : d602 q = 1) : d4408 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d602, d4408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d602, d4408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d604 q = 1) : d604 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d605 q = 1) : d4409 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d605, d4409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d605, d4409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d606 q = 1) : d51683 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d606, d51683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d606, d51683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d607 q = 1) : d51684 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d607, d51684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d607, d51684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d3537 q = 1) : d62579 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3537, d62579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d3537, d62579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro2085 (p : Pattern) (selected : d3545 p = 1) : d62585 p = 1 := by
  have h0 (q : Pattern) (selected : d3536 q = 1) : d3536 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d3538 q = 1) : d62580 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3538, d62580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3538, d62580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2084 q selected
  have h3 (q : Pattern) (selected : d3540 q = 1) : d3540 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d3541 q = 1) : d62581 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3541, d62581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3541, d62581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3542 q = 1) : d62582 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3542, d62582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3542, d62582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d3543 q = 1) : d62583 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3543, d62583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3543, d62583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3544 q = 1) : d62584 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3544, d62584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3544, d62584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d3545 q = 1) : d62585 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3545, d62585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d3545, d62585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h8 p selected
theorem eqIntro2086 (p : Pattern) (selected : d3551 p = 1) : d62591 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d3546 q = 1) : d62586 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3546, d62586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3546, d62586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2085 q selected
  have h2 (q : Pattern) (selected : d3547 q = 1) : d62587 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3547, d62587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3547, d62587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3548 q = 1) : d62588 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3548, d62588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3548, d62588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3549 q = 1) : d62589 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3549, d62589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3549, d62589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3550 q = 1) : d62590 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3550, d62590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3550, d62590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3551 q = 1) : d62591 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3551, d62591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3551, d62591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2087 (p : Pattern) (selected : d3554 p = 1) : d62593 p = 1 := by
  have h0 (q : Pattern) (selected : d810 q = 1) : d810 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d819 q = 1) : d819 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d852 q = 1) : d852 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d907 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro58 q selected
    | true =>
      simp only [d907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro59 q selected
  have h4 (q : Pattern) (selected : d908 q = 1) : d4446 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d908, d4446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d908, d4446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d910 q = 1) : d910 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d911 q = 1) : d4447 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d911, d4447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d911, d4447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d912 q = 1) : d51709 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d912, d51709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d912, d51709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d913 q = 1) : d51710 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d913, d51710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d913, d51710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d3554 q = 1) : d62593 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3554, d62593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d3554, d62593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro2088 (p : Pattern) (selected : d3562 p = 1) : d62599 p = 1 := by
  have h0 (q : Pattern) (selected : d3553 q = 1) : d3553 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d3555 q = 1) : d62594 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3555, d62594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3555, d62594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2087 q selected
  have h3 (q : Pattern) (selected : d3557 q = 1) : d3557 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d3558 q = 1) : d62595 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3558, d62595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3558, d62595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3559 q = 1) : d62596 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3559, d62596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3559, d62596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d3560 q = 1) : d62597 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3560, d62597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3560, d62597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3561 q = 1) : d62598 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3561, d62598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3561, d62598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d3562 q = 1) : d62599 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3562, d62599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d3562, d62599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h8 p selected
theorem eqIntro2089 (p : Pattern) (selected : d3568 p = 1) : d62605 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d3563 q = 1) : d62600 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3563, d62600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3563, d62600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2088 q selected
  have h2 (q : Pattern) (selected : d3564 q = 1) : d62601 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3564, d62601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3564, d62601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3565 q = 1) : d62602 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3565, d62602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3565, d62602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3566 q = 1) : d62603 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3566, d62603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3566, d62603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3567 q = 1) : d62604 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3567, d62604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3567, d62604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3568 q = 1) : d62605 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3568, d62605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3568, d62605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2090 (p : Pattern) (selected : d3572 p = 1) : d62608 p = 1 := by
  have h0 (q : Pattern) (selected : d1189 q = 1) : d1189 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1198 q = 1) : d1198 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1228 q = 1) : d1228 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d1318 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro88 q selected
    | true =>
      simp only [d1318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro89 q selected
  have h4 (q : Pattern) (selected : d1319 q = 1) : d4485 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1319, d4485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1319, d4485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1321 q = 1) : d1321 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d1322 q = 1) : d4486 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1322, d4486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1322, d4486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1323 q = 1) : d51736 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1323, d51736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1323, d51736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d1324 q = 1) : d51737 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1324, d51737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1324, d51737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d3572 q = 1) : d62608 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3572, d62608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d3572, d62608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro2091 (p : Pattern) (selected : d3580 p = 1) : d62614 p = 1 := by
  have h0 (q : Pattern) (selected : d3571 q = 1) : d3571 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d3573 q = 1) : d62609 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3573, d62609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3573, d62609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2090 q selected
  have h3 (q : Pattern) (selected : d3575 q = 1) : d3575 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d3576 q = 1) : d62610 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3576, d62610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3576, d62610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3577 q = 1) : d62611 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3577, d62611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3577, d62611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d3578 q = 1) : d62612 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3578, d62612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3578, d62612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3579 q = 1) : d62613 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3579, d62613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3579, d62613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d3580 q = 1) : d62614 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3580, d62614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d3580, d62614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h8 p selected
theorem eqIntro2092 (p : Pattern) (selected : d3586 p = 1) : d62620 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d3581 q = 1) : d62615 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3581, d62615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3581, d62615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2091 q selected
  have h2 (q : Pattern) (selected : d3582 q = 1) : d62616 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3582, d62616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3582, d62616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3583 q = 1) : d62617 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3583, d62617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3583, d62617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3584 q = 1) : d62618 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3584, d62618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3584, d62618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3585 q = 1) : d62619 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3585, d62619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3585, d62619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3586 q = 1) : d62620 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3586, d62620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3586, d62620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2093 (p : Pattern) (selected : d3591 p = 1) : d62624 p = 1 := by
  have h0 (q : Pattern) (selected : d1650 q = 1) : d1650 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1659 q = 1) : d1659 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1683 q = 1) : d1683 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d1795 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro124 q selected
    | true =>
      simp only [d1795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro125 q selected
  have h4 (q : Pattern) (selected : d1796 q = 1) : d4525 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1796, d4525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1796, d4525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1798 q = 1) : d1798 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d1799 q = 1) : d4526 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1799, d4526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1799, d4526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1800 q = 1) : d51764 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1800, d51764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1800, d51764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d1801 q = 1) : d51765 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1801, d51765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1801, d51765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d3591 q = 1) : d62624 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3591, d62624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d3591, d62624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro2094 (p : Pattern) (selected : d3599 p = 1) : d62630 p = 1 := by
  have h0 (q : Pattern) (selected : d3590 q = 1) : d3590 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d3592 q = 1) : d62625 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3592, d62625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3592, d62625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2093 q selected
  have h3 (q : Pattern) (selected : d3594 q = 1) : d3594 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d3595 q = 1) : d62626 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3595, d62626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3595, d62626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3596 q = 1) : d62627 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3596, d62627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3596, d62627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d3597 q = 1) : d62628 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3597, d62628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3597, d62628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3598 q = 1) : d62629 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3598, d62629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3598, d62629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d3599 q = 1) : d62630 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3599, d62630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d3599, d62630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h8 p selected
theorem eqIntro2095 (p : Pattern) (selected : d3605 p = 1) : d62636 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d3600 q = 1) : d62631 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3600, d62631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3600, d62631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2094 q selected
  have h2 (q : Pattern) (selected : d3601 q = 1) : d62632 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3601, d62632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3601, d62632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3602 q = 1) : d62633 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3602, d62633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3602, d62633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3603 q = 1) : d62634 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3603, d62634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3603, d62634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3604 q = 1) : d62635 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3604, d62635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3604, d62635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3605 q = 1) : d62636 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3605, d62636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3605, d62636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2096 (p : Pattern) (selected : d3611 p = 1) : d62641 p = 1 := by
  have h0 (q : Pattern) (selected : d2133 q = 1) : d2133 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2142 q = 1) : d2142 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d2162 q = 1) : d2162 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d2273 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro161 q selected
    | true =>
      simp only [d2273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro162 q selected
  have h4 (q : Pattern) (selected : d2274 q = 1) : d4566 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2274, d4566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2274, d4566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2276 q = 1) : d2276 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d2277 q = 1) : d4567 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2277, d4567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2277, d4567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2278 q = 1) : d51793 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2278, d51793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2278, d51793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d2279 q = 1) : d51794 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2279, d51794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2279, d51794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d3611 q = 1) : d62641 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d3611, d62641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d3611, d62641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro2097 (p : Pattern) (selected : d3619 p = 1) : d62647 p = 1 := by
  have h0 (q : Pattern) (selected : d3610 q = 1) : d3610 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d3612 q = 1) : d62642 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3612, d62642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3612, d62642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2096 q selected
  have h3 (q : Pattern) (selected : d3614 q = 1) : d3614 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d3615 q = 1) : d62643 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3615, d62643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3615, d62643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3616 q = 1) : d62644 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3616, d62644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3616, d62644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d3617 q = 1) : d62645 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3617, d62645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3617, d62645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3618 q = 1) : d62646 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3618, d62646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3618, d62646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d3619 q = 1) : d62647 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3619, d62647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d3619, d62647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h8 p selected
theorem eqIntro2098 (p : Pattern) (selected : d3625 p = 1) : d62653 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d3620 q = 1) : d62648 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3620, d62648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3620, d62648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2097 q selected
  have h2 (q : Pattern) (selected : d3621 q = 1) : d62649 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3621, d62649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3621, d62649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3622 q = 1) : d62650 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3622, d62650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3622, d62650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3623 q = 1) : d62651 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3623, d62651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3623, d62651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3624 q = 1) : d62652 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3624, d62652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3624, d62652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3625 q = 1) : d62653 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3625, d62653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3625, d62653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2099 (p : Pattern) (selected : d3631 p = 1) : d62659 p = 1 := by
  have h0 (q : Pattern) (selected : d3552 q = 1) : d62592 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3552, d62592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2083 q selected
    | true =>
      simp only [d3552, d62592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2086 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d3569 q = 1) : d62606 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3569, d62606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3569, d62606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2089 q selected
  have h3 (q : Pattern) (selected : d3570 q = 1) : d62607 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3570, d62607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3570, d62607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3587 q = 1) : d62621 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3587, d62621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3587, d62621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2092 q selected
  have h5 (q : Pattern) (selected : d3588 q = 1) : d62622 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3588, d62622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3588, d62622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3589 q = 1) : d62623 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3589, d62623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3589, d62623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3606 q = 1) : d62637 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3606, d62637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3606, d62637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2095 q selected
  have h8 (q : Pattern) (selected : d3607 q = 1) : d62638 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3607, d62638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3607, d62638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3608 q = 1) : d62639 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3608, d62639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3608, d62639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d3609 q = 1) : d62640 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d3609, d62640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3609, d62640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d3626 q = 1) : d62654 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3626, d62654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3626, d62654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2098 q selected
  have h12 (q : Pattern) (selected : d3627 q = 1) : d62655 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3627, d62655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3627, d62655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d3628 q = 1) : d62656 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3628, d62656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3628, d62656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d3629 q = 1) : d62657 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d3629, d62657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3629, d62657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d3630 q = 1) : d62658 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d3630, d62658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d3630, d62658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d3631 q = 1) : d62659 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d3631, d62659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d3631, d62659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro2100 (p : Pattern) (selected : d3637 p = 1) : d62665 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d3632 q = 1) : d62660 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d3632, d62660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2099 q selected
    | true =>
      simp only [d3632, d62660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3633 q = 1) : d62661 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d3633, d62661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3633, d62661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3634 q = 1) : d62662 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d3634, d62662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3634, d62662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3635 q = 1) : d62663 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d3635, d62663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3635, d62663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3636 q = 1) : d62664 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d3636, d62664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3636, d62664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3637 q = 1) : d62665 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d3637, d62665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3637, d62665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2101 (p : Pattern) (selected : d3643 p = 1) : d62671 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d3638 q = 1) : d62666 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d3638, d62666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2100 q selected
    | true =>
      simp only [d3638, d62666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3639 q = 1) : d62667 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d3639, d62667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3639, d62667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3640 q = 1) : d62668 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d3640, d62668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3640, d62668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3641 q = 1) : d62669 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d3641, d62669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3641, d62669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3642 q = 1) : d62670 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d3642, d62670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3642, d62670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3643 q = 1) : d62671 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d3643, d62671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3643, d62671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2102 (p : Pattern) (selected : d3649 p = 1) : d62677 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d3644 q = 1) : d62672 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d3644, d62672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2101 q selected
    | true =>
      simp only [d3644, d62672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3645 q = 1) : d62673 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d3645, d62673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3645, d62673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3646 q = 1) : d62674 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d3646, d62674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3646, d62674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3647 q = 1) : d62675 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d3647, d62675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3647, d62675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3648 q = 1) : d62676 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d3648, d62676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3648, d62676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3649 q = 1) : d62677 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d3649, d62677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3649, d62677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2103 (p : Pattern) (selected : d3655 p = 1) : d62683 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d3650 q = 1) : d62678 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d3650, d62678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2102 q selected
    | true =>
      simp only [d3650, d62678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3651 q = 1) : d62679 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d3651, d62679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3651, d62679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3652 q = 1) : d62680 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d3652, d62680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3652, d62680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3653 q = 1) : d62681 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d3653, d62681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3653, d62681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3654 q = 1) : d62682 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d3654, d62682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3654, d62682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3655 q = 1) : d62683 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d3655, d62683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3655, d62683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2104 (p : Pattern) (selected : d3661 p = 1) : d62689 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d3656 q = 1) : d62684 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d3656, d62684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2103 q selected
    | true =>
      simp only [d3656, d62684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3657 q = 1) : d62685 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d3657, d62685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3657, d62685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3658 q = 1) : d62686 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d3658, d62686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3658, d62686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3659 q = 1) : d62687 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d3659, d62687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3659, d62687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3660 q = 1) : d62688 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d3660, d62688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3660, d62688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3661 q = 1) : d62689 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d3661, d62689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3661, d62689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2105 (p : Pattern) (selected : d3667 p = 1) : d62695 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d3662 q = 1) : d62690 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d3662, d62690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2104 q selected
    | true =>
      simp only [d3662, d62690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3663 q = 1) : d62691 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d3663, d62691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3663, d62691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3664 q = 1) : d62692 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d3664, d62692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3664, d62692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3665 q = 1) : d62693 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d3665, d62693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3665, d62693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3666 q = 1) : d62694 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d3666, d62694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3666, d62694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3667 q = 1) : d62695 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d3667, d62695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3667, d62695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2106 (p : Pattern) (selected : d3673 p = 1) : d62701 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d3668 q = 1) : d62696 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d3668, d62696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2105 q selected
    | true =>
      simp only [d3668, d62696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3669 q = 1) : d62697 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d3669, d62697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3669, d62697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3670 q = 1) : d62698 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d3670, d62698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3670, d62698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3671 q = 1) : d62699 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d3671, d62699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3671, d62699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3672 q = 1) : d62700 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d3672, d62700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3672, d62700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3673 q = 1) : d62701 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d3673, d62701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3673, d62701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2107 (p : Pattern) (selected : d2784 p = 2) : d54865 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d105 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro658 q selected
  have h2 (q : Pattern) (selected : d106 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d112 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro658 q selected
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro659 q selected
  have h4 (q : Pattern) (selected : d113 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d114 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d212 q = 2) : d112 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212, d112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro672 q selected
    | true =>
      simp only [d212, d112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro677 q selected
  have h7 (q : Pattern) (selected : d214 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro678 q selected
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d215 q = 2) : d113 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d215, d113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d215, d113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d216 q = 2) : d53637 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d216, d53637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d216, d53637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d217 q = 2) : d53638 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d217, d53638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d217, d53638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d2783 q = 2) : d54864 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2783, d54864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d2783, d54864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d2784 q = 2) : d54865 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2784, d54865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d2784, d54865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h12 p selected
theorem eqIntro2108 (p : Pattern) (selected : d2791 p = 2) : d54872 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d285 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro688 q selected
  have h2 (q : Pattern) (selected : d286 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d292 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro688 q selected
    | true =>
      simp only [d292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro689 q selected
  have h4 (q : Pattern) (selected : d293 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d294 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d396 q = 2) : d292 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d396, d292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro702 q selected
    | true =>
      simp only [d396, d292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro707 q selected
  have h7 (q : Pattern) (selected : d398 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro708 q selected
    | true =>
      simp only [d398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro659 q selected
  have h8 (q : Pattern) (selected : d399 q = 2) : d293 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d399, d293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d399, d293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d400 q = 2) : d53653 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d400, d53653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d400, d53653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d401 q = 2) : d53654 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d401, d53654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d401, d53654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d2790 q = 2) : d54871 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2790, d54871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d2790, d54871, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d2791 q = 2) : d54872 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2791, d54872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d2791, d54872, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h12 p selected
theorem eqIntro2109 (p : Pattern) (selected : d2797 p = 2) : d54878 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2521 q = 2) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1210 q selected
  have h2 (q : Pattern) (selected : d2522 q = 2) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2523 q = 2) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2524 q = 2) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2785 q = 2) : d54866 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2785, d54866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2785, d54866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2107 q selected
  have h6 (q : Pattern) (selected : d2786 q = 2) : d54867 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2786, d54867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2786, d54867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2787 q = 2) : d54868 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2787, d54868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2787, d54868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d2788 q = 2) : d54869 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2788, d54869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2788, d54869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d2789 q = 2) : d54870 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2789, d54870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2789, d54870, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d2792 q = 2) : d54873 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2792, d54873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2792, d54873, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2108 q selected
  have h11 (q : Pattern) (selected : d2793 q = 2) : d54874 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2793, d54874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2793, d54874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d2794 q = 2) : d54875 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2794, d54875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2794, d54875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d2795 q = 2) : d54876 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2795, d54876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2795, d54876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d2796 q = 2) : d54877 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2796, d54877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2796, d54877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d2797 q = 2) : d54878 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2797, d54878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d2797, d54878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro2110 (p : Pattern) (selected : d2799 p = 2) : d54880 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d498 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro725 q selected
  have h2 (q : Pattern) (selected : d499 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d508 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro725 q selected
    | true =>
      simp only [d508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro728 q selected
  have h4 (q : Pattern) (selected : d509 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d510 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d632 q = 2) : d508 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d632, d508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro746 q selected
    | true =>
      simp only [d632, d508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro754 q selected
  have h7 (q : Pattern) (selected : d645 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro755 q selected
    | true =>
      simp only [d645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro756 q selected
  have h8 (q : Pattern) (selected : d646 q = 2) : d509 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d646, d509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d646, d509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d647 q = 2) : d53678 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d647, d53678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d647, d53678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d648 q = 2) : d53679 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d648, d53679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d648, d53679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d2798 q = 2) : d54879 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2798, d54879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d2798, d54879, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d2799 q = 2) : d54880 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2799, d54880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d2799, d54880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h12 p selected
theorem eqIntro2111 (p : Pattern) (selected : d2805 p = 2) : d54886 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2800 q = 2) : d54881 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2800, d54881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2800, d54881, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2110 q selected
  have h2 (q : Pattern) (selected : d2801 q = 2) : d54882 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2801, d54882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2801, d54882, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2802 q = 2) : d54883 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2802, d54883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2802, d54883, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2803 q = 2) : d54884 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2803, d54884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2803, d54884, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2804 q = 2) : d54885 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2804, d54885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2804, d54885, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2805 q = 2) : d54886 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2805, d54886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2805, d54886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2112 (p : Pattern) (selected : d2808 p = 2) : d54889 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d790 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro783 q selected
  have h2 (q : Pattern) (selected : d791 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d800 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro783 q selected
    | true =>
      simp only [d800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro786 q selected
  have h4 (q : Pattern) (selected : d801 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d802 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d938 q = 2) : d800 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d938, d800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro808 q selected
    | true =>
      simp only [d938, d800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro816 q selected
  have h7 (q : Pattern) (selected : d951 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro817 q selected
    | true =>
      simp only [d951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro818 q selected
  have h8 (q : Pattern) (selected : d952 q = 2) : d801 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d952, d801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d952, d801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d953 q = 2) : d53705 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d953, d53705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d953, d53705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d954 q = 2) : d53706 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d954, d53706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d954, d53706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d2807 q = 2) : d54888 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2807, d54888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d2807, d54888, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d2808 q = 2) : d54889 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2808, d54889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d2808, d54889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h12 p selected
theorem eqIntro2113 (p : Pattern) (selected : d2814 p = 2) : d54895 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2809 q = 2) : d54890 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2809, d54890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2809, d54890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2112 q selected
  have h2 (q : Pattern) (selected : d2810 q = 2) : d54891 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2810, d54891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2810, d54891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2811 q = 2) : d54892 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2811, d54892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2811, d54892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2812 q = 2) : d54893 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2812, d54893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2812, d54893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2813 q = 2) : d54894 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2813, d54894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2813, d54894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2814 q = 2) : d54895 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2814, d54895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2814, d54895, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2114 (p : Pattern) (selected : d2818 p = 2) : d54899 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1169 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro855 q selected
  have h2 (q : Pattern) (selected : d1170 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1179 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro855 q selected
    | true =>
      simp only [d1179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro858 q selected
  have h4 (q : Pattern) (selected : d1180 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1181 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1349 q = 2) : d1179 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1349, d1179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro884 q selected
    | true =>
      simp only [d1349, d1179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro892 q selected
  have h7 (q : Pattern) (selected : d1362 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro893 q selected
    | true =>
      simp only [d1362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro894 q selected
  have h8 (q : Pattern) (selected : d1363 q = 2) : d1180 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1363, d1180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1363, d1180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d1364 q = 2) : d53733 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1364, d53733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1364, d53733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d1365 q = 2) : d53734 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d1365, d53734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1365, d53734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d2817 q = 2) : d54898 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2817, d54898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d2817, d54898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d2818 q = 2) : d54899 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2818, d54899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d2818, d54899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h12 p selected
theorem eqIntro2115 (p : Pattern) (selected : d2824 p = 2) : d54905 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2819 q = 2) : d54900 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2819, d54900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2819, d54900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2114 q selected
  have h2 (q : Pattern) (selected : d2820 q = 2) : d54901 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2820, d54901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2820, d54901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2821 q = 2) : d54902 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2821, d54902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2821, d54902, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2822 q = 2) : d54903 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2822, d54903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2822, d54903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2823 q = 2) : d54904 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2823, d54904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2823, d54904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2824 q = 2) : d54905 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2824, d54905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2824, d54905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2116 (p : Pattern) (selected : d2829 p = 2) : d54910 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1630 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro937 q selected
  have h2 (q : Pattern) (selected : d1631 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1640 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro937 q selected
    | true =>
      simp only [d1640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro940 q selected
  have h4 (q : Pattern) (selected : d1641 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1642 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1826 q = 2) : d1640 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1826, d1640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro970 q selected
    | true =>
      simp only [d1826, d1640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro978 q selected
  have h7 (q : Pattern) (selected : d1839 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro979 q selected
    | true =>
      simp only [d1839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro980 q selected
  have h8 (q : Pattern) (selected : d1840 q = 2) : d1641 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1840, d1641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1840, d1641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d1841 q = 2) : d53762 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1841, d53762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1841, d53762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d1842 q = 2) : d53763 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d1842, d53763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1842, d53763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d2828 q = 2) : d54909 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2828, d54909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d2828, d54909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d2829 q = 2) : d54910 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2829, d54910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d2829, d54910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h12 p selected
theorem eqIntro2117 (p : Pattern) (selected : d2835 p = 2) : d54916 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2830 q = 2) : d54911 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2830, d54911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2830, d54911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2116 q selected
  have h2 (q : Pattern) (selected : d2831 q = 2) : d54912 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2831, d54912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2831, d54912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2832 q = 2) : d54913 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2832, d54913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2832, d54913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2833 q = 2) : d54914 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2833, d54914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2833, d54914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2834 q = 2) : d54915 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2834, d54915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2834, d54915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2835 q = 2) : d54916 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2835, d54916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2835, d54916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2118 (p : Pattern) (selected : d2841 p = 2) : d54922 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2113 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1026 q selected
  have h2 (q : Pattern) (selected : d2114 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2123 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1026 q selected
    | true =>
      simp only [d2123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1029 q selected
  have h4 (q : Pattern) (selected : d2124 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2125 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2304 q = 2) : d2123 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2304, d2123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1060 q selected
    | true =>
      simp only [d2304, d2123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1068 q selected
  have h7 (q : Pattern) (selected : d2317 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1069 q selected
    | true =>
      simp only [d2317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1070 q selected
  have h8 (q : Pattern) (selected : d2318 q = 2) : d2124 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2318, d2124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2318, d2124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d2319 q = 2) : d53792 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2319, d53792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d2319, d53792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d2320 q = 2) : d53793 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2320, d53793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2320, d53793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d2840 q = 2) : d54921 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2840, d54921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d2840, d54921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d2841 q = 2) : d54922 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2841, d54922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d2841, d54922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h12 p selected
theorem eqIntro2119 (p : Pattern) (selected : d2847 p = 2) : d54928 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2842 q = 2) : d54923 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2842, d54923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2842, d54923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2118 q selected
  have h2 (q : Pattern) (selected : d2843 q = 2) : d54924 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2843, d54924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2843, d54924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2844 q = 2) : d54925 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2844, d54925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2844, d54925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2845 q = 2) : d54926 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2845, d54926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2845, d54926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2846 q = 2) : d54927 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2846, d54927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2846, d54927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2847 q = 2) : d54928 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2847, d54928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2847, d54928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2120 (p : Pattern) (selected : d2853 p = 2) : d54934 p = 1 := by
  have h0 (q : Pattern) (selected : d2806 q = 2) : d54887 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d2806, d54887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2109 q selected
    | true =>
      simp only [d2806, d54887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2111 q selected
  have h1 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h2 (q : Pattern) (selected : d2815 q = 2) : d54896 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d2815, d54896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2815, d54896, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2113 q selected
  have h3 (q : Pattern) (selected : d2816 q = 2) : d54897 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d2816, d54897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2816, d54897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2825 q = 2) : d54906 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d2825, d54906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2825, d54906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2115 q selected
  have h5 (q : Pattern) (selected : d2826 q = 2) : d54907 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d2826, d54907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2826, d54907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2827 q = 2) : d54908 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d2827, d54908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2827, d54908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2836 q = 2) : d54917 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d2836, d54917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2836, d54917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2117 q selected
  have h8 (q : Pattern) (selected : d2837 q = 2) : d54918 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d2837, d54918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2837, d54918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d2838 q = 2) : d54919 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d2838, d54919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2838, d54919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d2839 q = 2) : d54920 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d2839, d54920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2839, d54920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d2848 q = 2) : d54929 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d2848, d54929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2848, d54929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2119 q selected
  have h12 (q : Pattern) (selected : d2849 q = 2) : d54930 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d2849, d54930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2849, d54930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d2850 q = 2) : d54931 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d2850, d54931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2850, d54931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d2851 q = 2) : d54932 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d2851, d54932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2851, d54932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d2852 q = 2) : d54933 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d2852, d54933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d2852, d54933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d2853 q = 2) : d54934 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d2853, d54934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d2853, d54934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro2121 (p : Pattern) (selected : d2859 p = 2) : d54940 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2854 q = 2) : d54935 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d2854, d54935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2120 q selected
    | true =>
      simp only [d2854, d54935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2855 q = 2) : d54936 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d2855, d54936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2855, d54936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2856 q = 2) : d54937 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d2856, d54937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2856, d54937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2857 q = 2) : d54938 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d2857, d54938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2857, d54938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2858 q = 2) : d54939 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d2858, d54939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2858, d54939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2859 q = 2) : d54940 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d2859, d54940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2859, d54940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2122 (p : Pattern) (selected : d2865 p = 2) : d54946 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2860 q = 2) : d54941 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d2860, d54941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2121 q selected
    | true =>
      simp only [d2860, d54941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2861 q = 2) : d54942 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d2861, d54942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2861, d54942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2862 q = 2) : d54943 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d2862, d54943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2862, d54943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2863 q = 2) : d54944 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d2863, d54944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2863, d54944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2864 q = 2) : d54945 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d2864, d54945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2864, d54945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2865 q = 2) : d54946 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d2865, d54946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2865, d54946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2123 (p : Pattern) (selected : d2871 p = 2) : d54952 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2866 q = 2) : d54947 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d2866, d54947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2122 q selected
    | true =>
      simp only [d2866, d54947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2867 q = 2) : d54948 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d2867, d54948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2867, d54948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2868 q = 2) : d54949 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d2868, d54949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2868, d54949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2869 q = 2) : d54950 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d2869, d54950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2869, d54950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2870 q = 2) : d54951 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d2870, d54951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2870, d54951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2871 q = 2) : d54952 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d2871, d54952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2871, d54952, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2124 (p : Pattern) (selected : d2877 p = 2) : d54958 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2872 q = 2) : d54953 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d2872, d54953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2123 q selected
    | true =>
      simp only [d2872, d54953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2873 q = 2) : d54954 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d2873, d54954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2873, d54954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2874 q = 2) : d54955 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d2874, d54955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2874, d54955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2875 q = 2) : d54956 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d2875, d54956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2875, d54956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2876 q = 2) : d54957 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d2876, d54957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2876, d54957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2877 q = 2) : d54958 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d2877, d54958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2877, d54958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2125 (p : Pattern) (selected : d2883 p = 2) : d54964 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2878 q = 2) : d54959 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d2878, d54959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2124 q selected
    | true =>
      simp only [d2878, d54959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2879 q = 2) : d54960 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d2879, d54960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2879, d54960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2880 q = 2) : d54961 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d2880, d54961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2880, d54961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2881 q = 2) : d54962 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d2881, d54962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2881, d54962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2882 q = 2) : d54963 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d2882, d54963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2882, d54963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2883 q = 2) : d54964 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d2883, d54964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2883, d54964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2126 (p : Pattern) (selected : d2889 p = 2) : d54970 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2884 q = 2) : d54965 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d2884, d54965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2125 q selected
    | true =>
      simp only [d2884, d54965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2885 q = 2) : d54966 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d2885, d54966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2885, d54966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2886 q = 2) : d54967 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d2886, d54967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2886, d54967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2887 q = 2) : d54968 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d2887, d54968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2887, d54968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2888 q = 2) : d54969 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d2888, d54969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2888, d54969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2889 q = 2) : d54970 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d2889, d54970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2889, d54970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2127 (p : Pattern) (selected : d2895 p = 2) : d54976 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2890 q = 2) : d54971 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d2890, d54971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2126 q selected
    | true =>
      simp only [d2890, d54971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2891 q = 2) : d54972 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d2891, d54972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2891, d54972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2892 q = 2) : d54973 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d2892, d54973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2892, d54973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2893 q = 2) : d54974 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d2893, d54974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2893, d54974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2894 q = 2) : d54975 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d2894, d54975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2894, d54975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2895 q = 2) : d54976 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d2895, d54976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2895, d54976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2128 (p : Pattern) (selected : d41 p = 0) : d51893 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d37 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro189 q selected
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d38 q = 0) : d51890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d39 q = 0) : d51891 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, d51891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d39, d51891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d40 q = 0) : d51892 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, d51892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d40, d51892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d41 q = 0) : d51893 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d41, d51893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d41, d51893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro2129 (p : Pattern) (selected : d62944 p = 0) : d63289 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d62940 q = 0) : d63285 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d62940, d63285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2128 q selected
    | true =>
      simp only [d62940, d63285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d62941 q = 0) : d63286 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d62941, d63286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d62941, d63286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d62942 q = 0) : d63287 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d62942, d63287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d62942, d63287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d62943 q = 0) : d63288 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d62943, d63288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d62943, d63288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d62944 q = 0) : d63289 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d62944, d63289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d62944, d63289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro2130 (p : Pattern) (selected : d62950 p = 0) : d63295 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d62945 q = 0) : d63290 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d62945, d63290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d62945, d63290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2129 q selected
  have h2 (q : Pattern) (selected : d62946 q = 0) : d63291 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62946, d63291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d62946, d63291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d62947 q = 0) : d63292 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d62947, d63292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d62947, d63292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d62948 q = 0) : d63293 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62948, d63293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d62948, d63293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d62949 q = 0) : d63294 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62949, d63294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d62949, d63294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d62950 q = 0) : d63295 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62950, d63295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d62950, d63295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2131 (p : Pattern) (selected : d62958 p = 0) : d63303 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d62940 q = 0) : d63285 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d62940, d63285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2128 q selected
    | true =>
      simp only [d62940, d63285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d62955 q = 0) : d63300 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d62955, d63300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d62955, d63300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d62956 q = 0) : d63301 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d62956, d63301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d62956, d63301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d62957 q = 0) : d63302 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d62957, d63302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d62957, d63302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d62958 q = 0) : d63303 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d62958, d63303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d62958, d63303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro2132 (p : Pattern) (selected : d115 p = 0) : d51967 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d37 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro189 q selected
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d38 q = 0) : d51890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d39 q = 0) : d51891 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, d51891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d39, d51891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d40 q = 0) : d51892 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d40, d51892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d40, d51892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d115 q = 0) : d51967 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d115, d51967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d115, d51967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro2133 (p : Pattern) (selected : d122 p = 0) : d51974 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d37 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro189 q selected
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d38 q = 0) : d51890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d39 q = 0) : d51891 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d39, d51891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d39, d51891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d121 q = 0) : d51973 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d121, d51973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d121, d51973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d122 q = 0) : d51974 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d122, d51974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d122, d51974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro2134 (p : Pattern) (selected : d155 p = 0) : d52006 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d151 q = 0) : d52002 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d52002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro207 q selected
    | true =>
      simp only [d151, d52002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d152 q = 0) : d52003 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d52003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152, d52003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
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
  have h5 (q : Pattern) (selected : d153 q = 0) : d52004 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d52004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153, d52004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154 q = 0) : d52005 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d52005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154, d52005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d155 q = 0) : d52006 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, d52006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d155, d52006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro2135 (p : Pattern) (selected : d186 p = 0) : d51893 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d182 q = 0) : d51889 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro212 q selected
    | true =>
      simp only [d182, d51889, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d183 q = 0) : d51890 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d183, d51890, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184 q = 0) : d51891 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d184, d51891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184, d51891, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185 q = 0) : d51892 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185, d51892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185, d51892, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d186 q = 0) : d51893 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d186, d51893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d186, d51893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro2136 (p : Pattern) (selected : d62974 p = 0) : d63318 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d62962 q = 0) : d63307 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d62962, d63307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2132 q selected
    | true =>
      simp only [d62962, d63307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d62963 q = 0) : d63308 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d62963, d63308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d62963, d63308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d62964 q = 0) : d63309 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d62964, d63309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d62964, d63309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d62965 q = 0) : d63310 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d62965, d63310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d62965, d63310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d62966 q = 0) : d63311 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d62966, d63311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2133 q selected
    | true =>
      simp only [d62966, d63311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d62967 q = 0) : d63312 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d62967, d63312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d62967, d63312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d62968 q = 0) : d63313 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d62968, d63313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d62968, d63313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d62969 q = 0) : d63314 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d62969, d63314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2134 q selected
    | true =>
      simp only [d62969, d63314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2128 q selected
  have h9 (q : Pattern) (selected : d62970 q = 0) : d63285 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d62970, d63285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2135 q selected
    | true =>
      simp only [d62970, d63285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d62971 q = 0) : d63315 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d62971, d63315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d62971, d63315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d62940 q = 0) : d63285 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d62940, d63285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2128 q selected
    | true =>
      simp only [d62940, d63285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d62941 q = 0) : d63286 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d62941, d63286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d62941, d63286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d62972 q = 0) : d63316 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d62972, d63316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d62972, d63316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d62973 q = 0) : d63317 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d62973, d63317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d62973, d63317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d62974 q = 0) : d63318 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d62974, d63318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d62974, d63318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro2137 (p : Pattern) (selected : d62981 p = 0) : d63325 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d62959 q = 0) : d63304 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d62959, d63304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d62959, d63304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2131 q selected
  have h2 (q : Pattern) (selected : d62960 q = 0) : d63305 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62960, d63305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d62960, d63305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d62961 q = 0) : d63306 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d62961, d63306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d62961, d63306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d62975 q = 0) : d63319 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d62975, d63319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d62975, d63319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2136 q selected
  have h5 (q : Pattern) (selected : d62976 q = 0) : d63320 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d62976, d63320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2131 q selected
    | true =>
      simp only [d62976, d63320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d62977 q = 0) : d63321 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62977, d63321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d62977, d63321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d62978 q = 0) : d63322 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d62978, d63322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d62978, d63322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d62979 q = 0) : d63323 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62979, d63323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d62979, d63323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d62980 q = 0) : d63324 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62980, d63324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d62980, d63324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d62981 q = 0) : d63325 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62981, d63325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d62981, d63325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro2138 (p : Pattern) (selected : d62990 p = 0) : d63334 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d62969 q = 0) : d63314 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d62969, d63314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2134 q selected
    | true =>
      simp only [d62969, d63314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2128 q selected
  have h2 (q : Pattern) (selected : d62987 q = 0) : d63331 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d62987, d63331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d62987, d63331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d62988 q = 0) : d63332 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d62988, d63332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d62988, d63332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d62989 q = 0) : d63333 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d62989, d63333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d62989, d63333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d62990 q = 0) : d63334 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d62990, d63334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d62990, d63334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro2139 (p : Pattern) (selected : d295 p = 0) : d52094 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d151 q = 0) : d52002 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d52002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro207 q selected
    | true =>
      simp only [d151, d52002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d152 q = 0) : d52003 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d52003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152, d52003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
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
  have h5 (q : Pattern) (selected : d153 q = 0) : d52004 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d52004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153, d52004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d154 q = 0) : d52005 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d52005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d154, d52005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d295 q = 0) : d52094 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d295, d52094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d295, d52094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro2140 (p : Pattern) (selected : d302 p = 0) : d52101 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d151 q = 0) : d52002 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d52002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro207 q selected
    | true =>
      simp only [d151, d52002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d152 q = 0) : d52003 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d52003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152, d52003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
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
  have h5 (q : Pattern) (selected : d153 q = 0) : d52004 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d52004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d153, d52004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d301 q = 0) : d52100 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, d52100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d301, d52100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d302 q = 0) : d52101 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, d52101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d302, d52101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro2141 (p : Pattern) (selected : d335 p = 0) : d52134 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d331 q = 0) : d52130 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d331, d52130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro237 q selected
    | true =>
      simp only [d331, d52130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d332 q = 0) : d52131 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d332, d52131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d332, d52131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d151 q = 0) : d52002 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d52002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro207 q selected
    | true =>
      simp only [d151, d52002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d152 q = 0) : d52003 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d52003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d152, d52003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d333 q = 0) : d52132 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d333, d52132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d333, d52132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d334 q = 0) : d52133 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d334, d52133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d334, d52133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d335 q = 0) : d52134 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d335, d52134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d335, d52134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro2142 (p : Pattern) (selected : d366 p = 0) : d52006 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d362 q = 0) : d52002 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d362, d52002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro242 q selected
    | true =>
      simp only [d362, d52002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d363 q = 0) : d52003 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d363, d52003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d363, d52003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
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
  have h5 (q : Pattern) (selected : d364 q = 0) : d52004 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d364, d52004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d364, d52004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d365 q = 0) : d52005 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d365, d52005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d365, d52005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d366 q = 0) : d52006 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d366, d52006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d366, d52006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro2143 (p : Pattern) (selected : d63008 p = 0) : d63351 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d62994 q = 0) : d63338 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d62994, d63338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2139 q selected
    | true =>
      simp only [d62994, d63338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2132 q selected
  have h2 (q : Pattern) (selected : d62995 q = 0) : d63339 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d62995, d63339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d62995, d63339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d62996 q = 0) : d63340 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d62996, d63340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d62996, d63340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d62997 q = 0) : d63341 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d62997, d63341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d62997, d63341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d62998 q = 0) : d63342 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d62998, d63342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2140 q selected
    | true =>
      simp only [d62998, d63342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2133 q selected
  have h6 (q : Pattern) (selected : d62999 q = 0) : d63343 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d62999, d63343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d62999, d63343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d63000 q = 0) : d63344 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d63000, d63344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d63000, d63344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d63001 q = 0) : d63345 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63001, d63345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2141 q selected
    | true =>
      simp only [d63001, d63345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2134 q selected
  have h9 (q : Pattern) (selected : d63002 q = 0) : d63314 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63002, d63314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2142 q selected
    | true =>
      simp only [d63002, d63314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2135 q selected
  have h10 (q : Pattern) (selected : d63003 q = 0) : d63346 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d63003, d63346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d63003, d63346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d63004 q = 0) : d63347 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63004, d63347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2134 q selected
    | true =>
      simp only [d63004, d63347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d63005 q = 0) : d63348 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d63005, d63348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d63005, d63348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d63006 q = 0) : d63349 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d63006, d63349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d63006, d63349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d63007 q = 0) : d63350 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d63007, d63350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d63007, d63350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d63008 q = 0) : d63351 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d63008, d63351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d63008, d63351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro2144 (p : Pattern) (selected : d63015 p = 0) : d63358 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d62991 q = 0) : d63335 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d62991, d63335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d62991, d63335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2138 q selected
  have h2 (q : Pattern) (selected : d62992 q = 0) : d63336 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62992, d63336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d62992, d63336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d62993 q = 0) : d63337 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d62993, d63337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d62993, d63337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d63009 q = 0) : d63352 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d63009, d63352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63009, d63352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2143 q selected
  have h5 (q : Pattern) (selected : d63010 q = 0) : d63353 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d63010, d63353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2138 q selected
    | true =>
      simp only [d63010, d63353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2131 q selected
  have h6 (q : Pattern) (selected : d63011 q = 0) : d63354 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d63011, d63354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d63011, d63354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d63012 q = 0) : d63355 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63012, d63355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d63012, d63355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d63013 q = 0) : d63356 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d63013, d63356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d63013, d63356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d63014 q = 0) : d63357 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d63014, d63357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d63014, d63357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d63015 q = 0) : d63358 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d63015, d63358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d63015, d63358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro2145 (p : Pattern) (selected : d63021 p = 0) : d63364 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d62951 q = 0) : d63296 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62951, d63296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d62951, d63296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2130 q selected
  have h2 (q : Pattern) (selected : d62952 q = 0) : d63297 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62952, d63297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d62952, d63297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d62953 q = 0) : d63298 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62953, d63298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d62953, d63298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d62954 q = 0) : d63299 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62954, d63299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d62954, d63299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d62982 q = 0) : d63326 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62982, d63326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d62982, d63326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2137 q selected
  have h6 (q : Pattern) (selected : d62983 q = 0) : d63327 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62983, d63327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d62983, d63327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d62984 q = 0) : d63328 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62984, d63328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d62984, d63328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d62985 q = 0) : d63329 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62985, d63329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d62985, d63329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d62986 q = 0) : d63330 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62986, d63330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d62986, d63330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d63016 q = 0) : d63359 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d63016, d63359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63016, d63359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2144 q selected
  have h11 (q : Pattern) (selected : d63017 q = 0) : d63360 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d63017, d63360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63017, d63360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d63018 q = 0) : d63361 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d63018, d63361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63018, d63361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d63019 q = 0) : d63362 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d63019, d63362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63019, d63362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d63020 q = 0) : d63363 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d63020, d63363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63020, d63363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d63021 q = 0) : d63364 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d63021, d63364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d63021, d63364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro2146 (p : Pattern) (selected : d486 p = 0) : d52233 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d478 q = 0) : d52225 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d52225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro263 q selected
    | true =>
      simp only [d478, d52225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d479 q = 0) : d52226 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d52226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d479, d52226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d482 q = 0) : d52229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro264 q selected
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d483 q = 0) : d52230 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d484 q = 0) : d52231 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d484, d52231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d484, d52231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d485 q = 0) : d52232 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d485, d52232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d485, d52232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d486 q = 0) : d52233 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d486, d52233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d486, d52233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro2147 (p : Pattern) (selected : d490 p = 0) : d52237 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d482 q = 0) : d52229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro264 q selected
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d483 q = 0) : d52230 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d488 q = 0) : d52235 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d52235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d488, d52235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d489 q = 0) : d52236 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d52236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d489, d52236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d490 q = 0) : d52237 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d52237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d490, d52237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro2148 (p : Pattern) (selected : d63026 p = 0) : d63369 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d63022 q = 0) : d63365 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63022, d63365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2146 q selected
    | true =>
      simp only [d63022, d63365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2147 q selected
  have h2 (q : Pattern) (selected : d63023 q = 0) : d63366 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d63023, d63366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63023, d63366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d63024 q = 0) : d63367 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d63024, d63367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d63024, d63367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d63025 q = 0) : d63368 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d63025, d63368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63025, d63368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d63026 q = 0) : d63369 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d63026, d63369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63026, d63369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro2149 (p : Pattern) (selected : d511 p = 0) : d52258 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d478 q = 0) : d52225 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d52225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro263 q selected
    | true =>
      simp only [d478, d52225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d479 q = 0) : d52226 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d52226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d479, d52226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d482 q = 0) : d52229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro264 q selected
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d483 q = 0) : d52230 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d484 q = 0) : d52231 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d484, d52231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d484, d52231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d485 q = 0) : d52232 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d485, d52232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d485, d52232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d511 q = 0) : d52258 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d511, d52258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d511, d52258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro2150 (p : Pattern) (selected : d513 p = 0) : d52260 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d482 q = 0) : d52229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro264 q selected
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d483 q = 0) : d52230 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d488 q = 0) : d52235 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d52235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d488, d52235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d489 q = 0) : d52236 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d52236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d489, d52236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d513 q = 0) : d52260 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d52260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d513, d52260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro2151 (p : Pattern) (selected : d520 p = 0) : d52267 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d478 q = 0) : d52225 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d52225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro263 q selected
    | true =>
      simp only [d478, d52225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d479 q = 0) : d52226 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d52226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d479, d52226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d482 q = 0) : d52229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro264 q selected
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d483 q = 0) : d52230 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d484 q = 0) : d52231 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d484, d52231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d484, d52231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d519 q = 0) : d52266 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d519, d52266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d519, d52266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d520 q = 0) : d52267 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d520, d52267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d520, d52267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro2152 (p : Pattern) (selected : d523 p = 0) : d52270 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d482 q = 0) : d52229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro264 q selected
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d483 q = 0) : d52230 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d488 q = 0) : d52235 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d52235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d488, d52235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d522 q = 0) : d52269 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d52269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d522, d52269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d523 q = 0) : d52270 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d52270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d523, d52270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro2153 (p : Pattern) (selected : d559 p = 0) : d52306 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d555 q = 0) : d52302 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d555, d52302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro279 q selected
    | true =>
      simp only [d555, d52302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d556 q = 0) : d52303 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d556, d52303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d556, d52303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d478 q = 0) : d52225 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d478, d52225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro263 q selected
    | true =>
      simp only [d478, d52225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d479 q = 0) : d52226 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d479, d52226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d479, d52226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d557 q = 0) : d52304 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d557, d52304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d557, d52304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d558 q = 0) : d52305 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d558, d52305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d558, d52305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d559 q = 0) : d52306 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d559, d52306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d559, d52306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro2154 (p : Pattern) (selected : d595 p = 0) : d52233 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d587 q = 0) : d52225 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d587, d52225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro284 q selected
    | true =>
      simp only [d587, d52225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d588 q = 0) : d52226 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d588, d52226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d588, d52226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d591 q = 0) : d52229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d591, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro285 q selected
    | true =>
      simp only [d591, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d592 q = 0) : d52230 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d592, d52230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d592, d52230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d593 q = 0) : d52231 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d593, d52231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d593, d52231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d594 q = 0) : d52232 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d594, d52232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d594, d52232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d595 q = 0) : d52233 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d595, d52233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d595, d52233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro2155 (p : Pattern) (selected : d599 p = 0) : d52237 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d591 q = 0) : d52229 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d591, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro285 q selected
    | true =>
      simp only [d591, d52229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d592 q = 0) : d52230 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d592, d52230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d592, d52230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d597 q = 0) : d52235 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d597, d52235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d597, d52235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d598 q = 0) : d52236 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d598, d52236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d598, d52236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d599 q = 0) : d52237 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d599, d52237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d599, d52237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro2156 (p : Pattern) (selected : d63044 p = 0) : d63386 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d63030 q = 0) : d63373 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63030, d63373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2149 q selected
    | true =>
      simp only [d63030, d63373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2150 q selected
  have h2 (q : Pattern) (selected : d63031 q = 0) : d63374 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d63031, d63374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63031, d63374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d63032 q = 0) : d63375 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d63032, d63375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d63032, d63375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d63033 q = 0) : d63376 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d63033, d63376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63033, d63376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d63034 q = 0) : d63377 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63034, d63377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2151 q selected
    | true =>
      simp only [d63034, d63377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2152 q selected
  have h6 (q : Pattern) (selected : d63035 q = 0) : d63378 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d63035, d63378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63035, d63378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d63036 q = 0) : d63379 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d63036, d63379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d63036, d63379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d63037 q = 0) : d63380 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63037, d63380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2153 q selected
    | true =>
      simp only [d63037, d63380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2146 q selected
  have h9 (q : Pattern) (selected : d63038 q = 0) : d63365 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63038, d63365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2154 q selected
    | true =>
      simp only [d63038, d63365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2155 q selected
  have h10 (q : Pattern) (selected : d63039 q = 0) : d63381 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d63039, d63381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d63039, d63381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d63040 q = 0) : d63382 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63040, d63382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2146 q selected
    | true =>
      simp only [d63040, d63382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d63041 q = 0) : d63383 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d63041, d63383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d63041, d63383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d63042 q = 0) : d63384 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d63042, d63384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d63042, d63384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d63043 q = 0) : d63385 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d63043, d63385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d63043, d63385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d63044 q = 0) : d63386 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d63044, d63386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d63044, d63386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro2157 (p : Pattern) (selected : d63050 p = 0) : d63392 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d63046 q = 0) : d63388 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63046, d63388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2147 q selected
    | true =>
      simp only [d63046, d63388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d63047 q = 0) : d63389 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d63047, d63389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63047, d63389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d63048 q = 0) : d63390 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d63048, d63390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d63048, d63390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d63049 q = 0) : d63391 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d63049, d63391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63049, d63391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d63050 q = 0) : d63392 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d63050, d63392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63050, d63392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro2158 (p : Pattern) (selected : d63056 p = 0) : d63398 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d63027 q = 0) : d63370 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d63027, d63370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63027, d63370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2148 q selected
  have h2 (q : Pattern) (selected : d63028 q = 0) : d63371 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d63028, d63371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d63028, d63371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d63029 q = 0) : d63372 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63029, d63372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63029, d63372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d63045 q = 0) : d63387 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d63045, d63387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63045, d63387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2156 q selected
  have h5 (q : Pattern) (selected : d63051 q = 0) : d63393 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d63051, d63393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2148 q selected
    | true =>
      simp only [d63051, d63393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2157 q selected
  have h6 (q : Pattern) (selected : d63052 q = 0) : d63394 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d63052, d63394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d63052, d63394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d63053 q = 0) : d63395 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63053, d63395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d63053, d63395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d63054 q = 0) : d63396 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d63054, d63396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d63054, d63396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d63055 q = 0) : d63397 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d63055, d63397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d63055, d63397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d63056 q = 0) : d63398 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d63056, d63398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d63056, d63398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro2159 (p : Pattern) (selected : d63062 p = 0) : d63404 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d63057 q = 0) : d63399 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d63057, d63399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63057, d63399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2158 q selected
  have h2 (q : Pattern) (selected : d63058 q = 0) : d63400 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d63058, d63400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63058, d63400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d63059 q = 0) : d63401 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d63059, d63401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63059, d63401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d63060 q = 0) : d63402 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d63060, d63402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63060, d63402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d63061 q = 0) : d63403 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d63061, d63403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63061, d63403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d63062 q = 0) : d63404 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d63062, d63404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63062, d63404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2160 (p : Pattern) (selected : d778 p = 0) : d52455 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d770 q = 0) : d52447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d52447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro321 q selected
    | true =>
      simp only [d770, d52447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d771 q = 0) : d52448 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d52448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d771, d52448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d774 q = 0) : d52451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro322 q selected
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d775 q = 0) : d52452 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d776 q = 0) : d52453 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, d52453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d776, d52453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d777 q = 0) : d52454 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d777, d52454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d777, d52454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d778 q = 0) : d52455 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d778, d52455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d778, d52455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro2161 (p : Pattern) (selected : d782 p = 0) : d52459 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d774 q = 0) : d52451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro322 q selected
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d775 q = 0) : d52452 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d780 q = 0) : d52457 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d52457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d780, d52457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d781 q = 0) : d52458 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d52458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d781, d52458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d782 q = 0) : d52459 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, d52459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d782, d52459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro2162 (p : Pattern) (selected : d63068 p = 0) : d63410 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d63064 q = 0) : d63406 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63064, d63406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2160 q selected
    | true =>
      simp only [d63064, d63406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2161 q selected
  have h2 (q : Pattern) (selected : d63065 q = 0) : d63407 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d63065, d63407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63065, d63407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d63066 q = 0) : d63408 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d63066, d63408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d63066, d63408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d63067 q = 0) : d63409 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d63067, d63409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63067, d63409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d63068 q = 0) : d63410 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d63068, d63410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63068, d63410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro2163 (p : Pattern) (selected : d803 p = 0) : d52480 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d770 q = 0) : d52447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d52447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro321 q selected
    | true =>
      simp only [d770, d52447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d771 q = 0) : d52448 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d52448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d771, d52448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d774 q = 0) : d52451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro322 q selected
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d775 q = 0) : d52452 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d776 q = 0) : d52453 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, d52453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d776, d52453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d777 q = 0) : d52454 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d777, d52454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d777, d52454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d803 q = 0) : d52480 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d803, d52480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d803, d52480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro2164 (p : Pattern) (selected : d805 p = 0) : d52482 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d774 q = 0) : d52451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro322 q selected
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d775 q = 0) : d52452 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d780 q = 0) : d52457 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d52457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d780, d52457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d781 q = 0) : d52458 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d52458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d781, d52458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d805 q = 0) : d52482 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d52482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d805, d52482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro2165 (p : Pattern) (selected : d812 p = 0) : d52489 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d770 q = 0) : d52447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d52447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro321 q selected
    | true =>
      simp only [d770, d52447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d771 q = 0) : d52448 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d52448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d771, d52448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d774 q = 0) : d52451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro322 q selected
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d775 q = 0) : d52452 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d776 q = 0) : d52453 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, d52453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d776, d52453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d811 q = 0) : d52488 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d811, d52488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d811, d52488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d812 q = 0) : d52489 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d812, d52489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d812, d52489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro2166 (p : Pattern) (selected : d815 p = 0) : d52492 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d774 q = 0) : d52451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro322 q selected
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d775 q = 0) : d52452 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d780 q = 0) : d52457 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d52457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d780, d52457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d814 q = 0) : d52491 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d52491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d814, d52491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d815 q = 0) : d52492 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d52492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d815, d52492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro2167 (p : Pattern) (selected : d850 p = 0) : d52527 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d846 q = 0) : d52523 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d846, d52523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro337 q selected
    | true =>
      simp only [d846, d52523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d847 q = 0) : d52524 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d847, d52524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d847, d52524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d770 q = 0) : d52447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d52447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro321 q selected
    | true =>
      simp only [d770, d52447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d771 q = 0) : d52448 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d52448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d771, d52448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d848 q = 0) : d52525 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d848, d52525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d848, d52525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d849 q = 0) : d52526 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d849, d52526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d849, d52526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d850 q = 0) : d52527 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d850, d52527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d850, d52527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro2168 (p : Pattern) (selected : d901 p = 0) : d52455 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d893 q = 0) : d52447 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d893, d52447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro346 q selected
    | true =>
      simp only [d893, d52447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d894 q = 0) : d52448 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d894, d52448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d894, d52448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d897 q = 0) : d52451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d897, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro347 q selected
    | true =>
      simp only [d897, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d898 q = 0) : d52452 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d898, d52452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d898, d52452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d899 q = 0) : d52453 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d899, d52453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d899, d52453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d900 q = 0) : d52454 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d900, d52454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d900, d52454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d901 q = 0) : d52455 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d901, d52455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d901, d52455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro2169 (p : Pattern) (selected : d905 p = 0) : d52459 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d897 q = 0) : d52451 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d897, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro347 q selected
    | true =>
      simp only [d897, d52451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d898 q = 0) : d52452 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d898, d52452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d898, d52452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d903 q = 0) : d52457 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d903, d52457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d903, d52457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d904 q = 0) : d52458 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d904, d52458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d904, d52458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d905 q = 0) : d52459 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d905, d52459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d905, d52459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro2170 (p : Pattern) (selected : d63086 p = 0) : d63427 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d63072 q = 0) : d63414 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63072, d63414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2163 q selected
    | true =>
      simp only [d63072, d63414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2164 q selected
  have h2 (q : Pattern) (selected : d63073 q = 0) : d63415 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d63073, d63415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63073, d63415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d63074 q = 0) : d63416 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d63074, d63416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d63074, d63416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d63075 q = 0) : d63417 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d63075, d63417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63075, d63417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d63076 q = 0) : d63418 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63076, d63418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2165 q selected
    | true =>
      simp only [d63076, d63418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2166 q selected
  have h6 (q : Pattern) (selected : d63077 q = 0) : d63419 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d63077, d63419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63077, d63419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d63078 q = 0) : d63420 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d63078, d63420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d63078, d63420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d63079 q = 0) : d63421 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63079, d63421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2167 q selected
    | true =>
      simp only [d63079, d63421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2160 q selected
  have h9 (q : Pattern) (selected : d63080 q = 0) : d63406 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63080, d63406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2168 q selected
    | true =>
      simp only [d63080, d63406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2169 q selected
  have h10 (q : Pattern) (selected : d63081 q = 0) : d63422 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d63081, d63422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d63081, d63422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d63082 q = 0) : d63423 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63082, d63423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2160 q selected
    | true =>
      simp only [d63082, d63423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d63083 q = 0) : d63424 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d63083, d63424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d63083, d63424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d63084 q = 0) : d63425 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d63084, d63425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d63084, d63425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d63085 q = 0) : d63426 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d63085, d63426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d63085, d63426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d63086 q = 0) : d63427 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d63086, d63427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d63086, d63427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro2171 (p : Pattern) (selected : d63092 p = 0) : d63433 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d63088 q = 0) : d63429 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63088, d63429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2161 q selected
    | true =>
      simp only [d63088, d63429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d63089 q = 0) : d63430 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d63089, d63430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63089, d63430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d63090 q = 0) : d63431 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d63090, d63431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d63090, d63431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d63091 q = 0) : d63432 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d63091, d63432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63091, d63432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d63092 q = 0) : d63433 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d63092, d63433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63092, d63433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro2172 (p : Pattern) (selected : d63098 p = 0) : d63439 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d63069 q = 0) : d63411 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d63069, d63411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63069, d63411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2162 q selected
  have h2 (q : Pattern) (selected : d63070 q = 0) : d63412 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d63070, d63412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d63070, d63412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d63071 q = 0) : d63413 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63071, d63413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63071, d63413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d63087 q = 0) : d63428 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d63087, d63428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63087, d63428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2170 q selected
  have h5 (q : Pattern) (selected : d63093 q = 0) : d63434 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d63093, d63434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2162 q selected
    | true =>
      simp only [d63093, d63434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2171 q selected
  have h6 (q : Pattern) (selected : d63094 q = 0) : d63435 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d63094, d63435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d63094, d63435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d63095 q = 0) : d63436 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63095, d63436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d63095, d63436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d63096 q = 0) : d63437 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d63096, d63437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d63096, d63437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d63097 q = 0) : d63438 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d63097, d63438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d63097, d63438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d63098 q = 0) : d63439 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d63098, d63439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d63098, d63439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro2173 (p : Pattern) (selected : d63104 p = 0) : d63445 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d63099 q = 0) : d63440 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d63099, d63440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63099, d63440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2172 q selected
  have h2 (q : Pattern) (selected : d63100 q = 0) : d63441 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d63100, d63441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63100, d63441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d63101 q = 0) : d63442 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d63101, d63442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63101, d63442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d63102 q = 0) : d63443 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d63102, d63443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63102, d63443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d63103 q = 0) : d63444 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d63103, d63444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63103, d63444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d63104 q = 0) : d63445 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d63104, d63445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63104, d63445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2174 (p : Pattern) (selected : d1157 p = 0) : d52738 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1149 q = 0) : d52730 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d52730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro393 q selected
    | true =>
      simp only [d1149, d52730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1150 q = 0) : d52731 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d52731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1150, d52731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1153 q = 0) : d52734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro394 q selected
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1154 q = 0) : d52735 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1155 q = 0) : d52736 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d52736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1155, d52736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1156 q = 0) : d52737 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1156, d52737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1156, d52737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1157 q = 0) : d52738 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1157, d52738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1157, d52738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro2175 (p : Pattern) (selected : d1161 p = 0) : d52742 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1153 q = 0) : d52734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro394 q selected
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1154 q = 0) : d52735 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1159 q = 0) : d52740 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d52740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1159, d52740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1160 q = 0) : d52741 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, d52741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1160, d52741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1161 q = 0) : d52742 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1161, d52742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1161, d52742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro2176 (p : Pattern) (selected : d63111 p = 0) : d63452 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d63107 q = 0) : d63448 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63107, d63448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2174 q selected
    | true =>
      simp only [d63107, d63448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2175 q selected
  have h2 (q : Pattern) (selected : d63108 q = 0) : d63449 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d63108, d63449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63108, d63449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d63109 q = 0) : d63450 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d63109, d63450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d63109, d63450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d63110 q = 0) : d63451 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d63110, d63451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63110, d63451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d63111 q = 0) : d63452 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d63111, d63452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63111, d63452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro2177 (p : Pattern) (selected : d1182 p = 0) : d52763 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1149 q = 0) : d52730 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d52730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro393 q selected
    | true =>
      simp only [d1149, d52730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1150 q = 0) : d52731 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d52731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1150, d52731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1153 q = 0) : d52734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro394 q selected
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1154 q = 0) : d52735 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1155 q = 0) : d52736 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d52736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1155, d52736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1156 q = 0) : d52737 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1156, d52737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1156, d52737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1182 q = 0) : d52763 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1182, d52763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1182, d52763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro2178 (p : Pattern) (selected : d1184 p = 0) : d52765 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1153 q = 0) : d52734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro394 q selected
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1154 q = 0) : d52735 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1159 q = 0) : d52740 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d52740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1159, d52740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1160 q = 0) : d52741 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, d52741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1160, d52741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1184 q = 0) : d52765 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1184, d52765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1184, d52765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro2179 (p : Pattern) (selected : d1191 p = 0) : d52772 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1149 q = 0) : d52730 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d52730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro393 q selected
    | true =>
      simp only [d1149, d52730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1150 q = 0) : d52731 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d52731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1150, d52731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1153 q = 0) : d52734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro394 q selected
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1154 q = 0) : d52735 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1155 q = 0) : d52736 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d52736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1155, d52736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1190 q = 0) : d52771 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1190, d52771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1190, d52771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1191 q = 0) : d52772 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1191, d52772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1191, d52772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro2180 (p : Pattern) (selected : d1194 p = 0) : d52775 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1153 q = 0) : d52734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro394 q selected
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1154 q = 0) : d52735 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1159 q = 0) : d52740 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d52740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1159, d52740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1193 q = 0) : d52774 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1193, d52774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1193, d52774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1194 q = 0) : d52775 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1194, d52775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1194, d52775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro2181 (p : Pattern) (selected : d1226 p = 0) : d52807 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1222 q = 0) : d52803 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1222, d52803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro409 q selected
    | true =>
      simp only [d1222, d52803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1223 q = 0) : d52804 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1223, d52804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1223, d52804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1149 q = 0) : d52730 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d52730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro393 q selected
    | true =>
      simp only [d1149, d52730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1150 q = 0) : d52731 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d52731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1150, d52731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1224 q = 0) : d52805 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1224, d52805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1224, d52805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1225 q = 0) : d52806 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1225, d52806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1225, d52806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1226 q = 0) : d52807 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1226, d52807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1226, d52807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro2182 (p : Pattern) (selected : d1312 p = 0) : d52738 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1304 q = 0) : d52730 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1304, d52730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro422 q selected
    | true =>
      simp only [d1304, d52730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1305 q = 0) : d52731 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1305, d52731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1305, d52731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1308 q = 0) : d52734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1308, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro423 q selected
    | true =>
      simp only [d1308, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1309 q = 0) : d52735 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1309, d52735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1309, d52735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1310 q = 0) : d52736 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1310, d52736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1310, d52736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1311 q = 0) : d52737 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1311, d52737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1311, d52737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1312 q = 0) : d52738 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1312, d52738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1312, d52738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro2183 (p : Pattern) (selected : d1316 p = 0) : d52742 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1308 q = 0) : d52734 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1308, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro423 q selected
    | true =>
      simp only [d1308, d52734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1309 q = 0) : d52735 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1309, d52735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1309, d52735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1314 q = 0) : d52740 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1314, d52740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1314, d52740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1315 q = 0) : d52741 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1315, d52741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1315, d52741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1316 q = 0) : d52742 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1316, d52742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1316, d52742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro2184 (p : Pattern) (selected : d63129 p = 0) : d63469 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d63115 q = 0) : d63456 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63115, d63456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2177 q selected
    | true =>
      simp only [d63115, d63456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2178 q selected
  have h2 (q : Pattern) (selected : d63116 q = 0) : d63457 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d63116, d63457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63116, d63457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d63117 q = 0) : d63458 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d63117, d63458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d63117, d63458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d63118 q = 0) : d63459 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d63118, d63459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63118, d63459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d63119 q = 0) : d63460 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63119, d63460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2179 q selected
    | true =>
      simp only [d63119, d63460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2180 q selected
  have h6 (q : Pattern) (selected : d63120 q = 0) : d63461 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d63120, d63461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63120, d63461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d63121 q = 0) : d63462 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d63121, d63462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d63121, d63462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d63122 q = 0) : d63463 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63122, d63463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2181 q selected
    | true =>
      simp only [d63122, d63463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2174 q selected
  have h9 (q : Pattern) (selected : d63123 q = 0) : d63448 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63123, d63448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2182 q selected
    | true =>
      simp only [d63123, d63448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2183 q selected
  have h10 (q : Pattern) (selected : d63124 q = 0) : d63464 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d63124, d63464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d63124, d63464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d63125 q = 0) : d63465 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63125, d63465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2174 q selected
    | true =>
      simp only [d63125, d63465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d63126 q = 0) : d63466 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d63126, d63466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d63126, d63466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d63127 q = 0) : d63467 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d63127, d63467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d63127, d63467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d63128 q = 0) : d63468 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d63128, d63468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d63128, d63468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d63129 q = 0) : d63469 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d63129, d63469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d63129, d63469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro2185 (p : Pattern) (selected : d63135 p = 0) : d63475 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d63131 q = 0) : d63471 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63131, d63471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2175 q selected
    | true =>
      simp only [d63131, d63471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d63132 q = 0) : d63472 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d63132, d63472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63132, d63472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d63133 q = 0) : d63473 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d63133, d63473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d63133, d63473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d63134 q = 0) : d63474 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d63134, d63474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63134, d63474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d63135 q = 0) : d63475 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d63135, d63475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63135, d63475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro2186 (p : Pattern) (selected : d63141 p = 0) : d63481 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d63112 q = 0) : d63453 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d63112, d63453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63112, d63453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2176 q selected
  have h2 (q : Pattern) (selected : d63113 q = 0) : d63454 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d63113, d63454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d63113, d63454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d63114 q = 0) : d63455 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63114, d63455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63114, d63455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d63130 q = 0) : d63470 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d63130, d63470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63130, d63470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2184 q selected
  have h5 (q : Pattern) (selected : d63136 q = 0) : d63476 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d63136, d63476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2176 q selected
    | true =>
      simp only [d63136, d63476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2185 q selected
  have h6 (q : Pattern) (selected : d63137 q = 0) : d63477 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d63137, d63477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d63137, d63477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d63138 q = 0) : d63478 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63138, d63478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d63138, d63478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d63139 q = 0) : d63479 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d63139, d63479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d63139, d63479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d63140 q = 0) : d63480 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d63140, d63480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d63140, d63480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d63141 q = 0) : d63481 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d63141, d63481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d63141, d63481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro2187 (p : Pattern) (selected : d63147 p = 0) : d63487 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d63142 q = 0) : d63482 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d63142, d63482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63142, d63482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2186 q selected
  have h2 (q : Pattern) (selected : d63143 q = 0) : d63483 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d63143, d63483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63143, d63483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d63144 q = 0) : d63484 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d63144, d63484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63144, d63484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d63145 q = 0) : d63485 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d63145, d63485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63145, d63485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d63146 q = 0) : d63486 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d63146, d63486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63146, d63486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d63147 q = 0) : d63487 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d63147, d63487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63147, d63487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2188 (p : Pattern) (selected : d1618 p = 0) : d53059 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1610 q = 0) : d53051 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d53051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro475 q selected
    | true =>
      simp only [d1610, d53051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1611 q = 0) : d53052 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d53052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1611, d53052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1614 q = 0) : d53055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro476 q selected
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1615 q = 0) : d53056 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1616 q = 0) : d53057 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d53057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1616, d53057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1617 q = 0) : d53058 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1617, d53058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1617, d53058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1618 q = 0) : d53059 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1618, d53059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1618, d53059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro2189 (p : Pattern) (selected : d1622 p = 0) : d53063 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1614 q = 0) : d53055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro476 q selected
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1615 q = 0) : d53056 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1620 q = 0) : d53061 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d53061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1620, d53061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1621 q = 0) : d53062 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, d53062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1621, d53062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1622 q = 0) : d53063 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1622, d53063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1622, d53063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro2190 (p : Pattern) (selected : d63155 p = 0) : d63495 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d63151 q = 0) : d63491 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63151, d63491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2188 q selected
    | true =>
      simp only [d63151, d63491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2189 q selected
  have h2 (q : Pattern) (selected : d63152 q = 0) : d63492 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d63152, d63492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63152, d63492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d63153 q = 0) : d63493 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d63153, d63493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d63153, d63493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d63154 q = 0) : d63494 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d63154, d63494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63154, d63494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d63155 q = 0) : d63495 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d63155, d63495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63155, d63495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro2191 (p : Pattern) (selected : d1643 p = 0) : d53084 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1610 q = 0) : d53051 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d53051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro475 q selected
    | true =>
      simp only [d1610, d53051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1611 q = 0) : d53052 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d53052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1611, d53052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1614 q = 0) : d53055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro476 q selected
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1615 q = 0) : d53056 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1616 q = 0) : d53057 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d53057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1616, d53057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1617 q = 0) : d53058 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1617, d53058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1617, d53058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1643 q = 0) : d53084 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1643, d53084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1643, d53084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro2192 (p : Pattern) (selected : d1645 p = 0) : d53086 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1614 q = 0) : d53055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro476 q selected
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1615 q = 0) : d53056 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1620 q = 0) : d53061 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d53061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1620, d53061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1621 q = 0) : d53062 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, d53062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1621, d53062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1645 q = 0) : d53086 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1645, d53086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1645, d53086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro2193 (p : Pattern) (selected : d1652 p = 0) : d53093 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1610 q = 0) : d53051 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d53051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro475 q selected
    | true =>
      simp only [d1610, d53051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1611 q = 0) : d53052 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d53052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1611, d53052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1614 q = 0) : d53055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro476 q selected
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1615 q = 0) : d53056 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1616 q = 0) : d53057 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d53057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1616, d53057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1651 q = 0) : d53092 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1651, d53092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1651, d53092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d1652 q = 0) : d53093 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1652, d53093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1652, d53093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro2194 (p : Pattern) (selected : d1655 p = 0) : d53096 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1614 q = 0) : d53055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro476 q selected
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1615 q = 0) : d53056 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1620 q = 0) : d53061 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d53061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1620, d53061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1654 q = 0) : d53095 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1654, d53095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1654, d53095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1655 q = 0) : d53096 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1655, d53096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1655, d53096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro2195 (p : Pattern) (selected : d1681 p = 0) : d53122 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1677 q = 0) : d53118 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1677, d53118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro489 q selected
    | true =>
      simp only [d1677, d53118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1678 q = 0) : d53119 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1678, d53119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1678, d53119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1610 q = 0) : d53051 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d53051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro475 q selected
    | true =>
      simp only [d1610, d53051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1611 q = 0) : d53052 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d53052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1611, d53052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1679 q = 0) : d53120 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1679, d53120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1679, d53120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1680 q = 0) : d53121 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1680, d53121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1680, d53121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1681 q = 0) : d53122 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1681, d53122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1681, d53122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro2196 (p : Pattern) (selected : d1789 p = 0) : d53059 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1781 q = 0) : d53051 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1781, d53051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro508 q selected
    | true =>
      simp only [d1781, d53051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1782 q = 0) : d53052 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1782, d53052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1782, d53052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1785 q = 0) : d53055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1785, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro509 q selected
    | true =>
      simp only [d1785, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1786 q = 0) : d53056 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1786, d53056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1786, d53056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1787 q = 0) : d53057 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1787, d53057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1787, d53057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1788 q = 0) : d53058 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1788, d53058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1788, d53058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1789 q = 0) : d53059 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1789, d53059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1789, d53059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro2197 (p : Pattern) (selected : d1793 p = 0) : d53063 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1785 q = 0) : d53055 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1785, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro509 q selected
    | true =>
      simp only [d1785, d53055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1786 q = 0) : d53056 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1786, d53056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1786, d53056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1791 q = 0) : d53061 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1791, d53061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1791, d53061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1792 q = 0) : d53062 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1792, d53062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1792, d53062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1793 q = 0) : d53063 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1793, d53063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1793, d53063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro2198 (p : Pattern) (selected : d63173 p = 0) : d63512 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d63159 q = 0) : d63499 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63159, d63499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2191 q selected
    | true =>
      simp only [d63159, d63499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2192 q selected
  have h2 (q : Pattern) (selected : d63160 q = 0) : d63500 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d63160, d63500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63160, d63500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d63161 q = 0) : d63501 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d63161, d63501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d63161, d63501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d63162 q = 0) : d63502 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d63162, d63502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63162, d63502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d63163 q = 0) : d63503 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63163, d63503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2193 q selected
    | true =>
      simp only [d63163, d63503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2194 q selected
  have h6 (q : Pattern) (selected : d63164 q = 0) : d63504 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d63164, d63504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63164, d63504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d63165 q = 0) : d63505 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d63165, d63505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d63165, d63505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d63166 q = 0) : d63506 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63166, d63506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2195 q selected
    | true =>
      simp only [d63166, d63506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2188 q selected
  have h9 (q : Pattern) (selected : d63167 q = 0) : d63491 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63167, d63491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2196 q selected
    | true =>
      simp only [d63167, d63491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2197 q selected
  have h10 (q : Pattern) (selected : d63168 q = 0) : d63507 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d63168, d63507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d63168, d63507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d63169 q = 0) : d63508 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63169, d63508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2188 q selected
    | true =>
      simp only [d63169, d63508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d63170 q = 0) : d63509 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d63170, d63509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d63170, d63509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d63171 q = 0) : d63510 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d63171, d63510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d63171, d63510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d63172 q = 0) : d63511 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d63172, d63511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d63172, d63511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d63173 q = 0) : d63512 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d63173, d63512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d63173, d63512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro2199 (p : Pattern) (selected : d63179 p = 0) : d63518 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d63175 q = 0) : d63514 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63175, d63514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2189 q selected
    | true =>
      simp only [d63175, d63514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d63176 q = 0) : d63515 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d63176, d63515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63176, d63515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d63177 q = 0) : d63516 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d63177, d63516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d63177, d63516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d63178 q = 0) : d63517 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d63178, d63517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63178, d63517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d63179 q = 0) : d63518 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d63179, d63518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63179, d63518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro2200 (p : Pattern) (selected : d63185 p = 0) : d63524 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d63156 q = 0) : d63496 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d63156, d63496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63156, d63496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2190 q selected
  have h2 (q : Pattern) (selected : d63157 q = 0) : d63497 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d63157, d63497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d63157, d63497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d63158 q = 0) : d63498 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63158, d63498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63158, d63498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d63174 q = 0) : d63513 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d63174, d63513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63174, d63513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2198 q selected
  have h5 (q : Pattern) (selected : d63180 q = 0) : d63519 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d63180, d63519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2190 q selected
    | true =>
      simp only [d63180, d63519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2199 q selected
  have h6 (q : Pattern) (selected : d63181 q = 0) : d63520 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d63181, d63520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d63181, d63520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d63182 q = 0) : d63521 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63182, d63521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d63182, d63521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d63183 q = 0) : d63522 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d63183, d63522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d63183, d63522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d63184 q = 0) : d63523 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d63184, d63523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d63184, d63523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d63185 q = 0) : d63524 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d63185, d63524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d63185, d63524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro2201 (p : Pattern) (selected : d63191 p = 0) : d63530 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d63186 q = 0) : d63525 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d63186, d63525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63186, d63525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2200 q selected
  have h2 (q : Pattern) (selected : d63187 q = 0) : d63526 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d63187, d63526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63187, d63526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d63188 q = 0) : d63527 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d63188, d63527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63188, d63527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d63189 q = 0) : d63528 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d63189, d63528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63189, d63528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d63190 q = 0) : d63529 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d63190, d63529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63190, d63529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d63191 q = 0) : d63530 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d63191, d63530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63191, d63530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2202 (p : Pattern) (selected : d2101 p = 0) : d53380 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2093 q = 0) : d53372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro564 q selected
    | true =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2094 q = 0) : d53373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d53373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2094, d53373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2097 q = 0) : d53376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro565 q selected
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2098 q = 0) : d53377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2099 q = 0) : d53378 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, d53378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2099, d53378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2100 q = 0) : d53379 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2100, d53379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2100, d53379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2101 q = 0) : d53380 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2101, d53380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2101, d53380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro2203 (p : Pattern) (selected : d2105 p = 0) : d53384 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2097 q = 0) : d53376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro565 q selected
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2098 q = 0) : d53377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2103 q = 0) : d53382 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d53382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2103, d53382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2104 q = 0) : d53383 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, d53383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2104, d53383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2105 q = 0) : d53384 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2105, d53384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2105, d53384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro2204 (p : Pattern) (selected : d63200 p = 0) : d63539 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d63196 q = 0) : d63535 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63196, d63535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2202 q selected
    | true =>
      simp only [d63196, d63535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2203 q selected
  have h2 (q : Pattern) (selected : d63197 q = 0) : d63536 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d63197, d63536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63197, d63536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d63198 q = 0) : d63537 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d63198, d63537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d63198, d63537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d63199 q = 0) : d63538 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d63199, d63538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63199, d63538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d63200 q = 0) : d63539 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d63200, d63539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63200, d63539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro2205 (p : Pattern) (selected : d2126 p = 0) : d53405 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2093 q = 0) : d53372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro564 q selected
    | true =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2094 q = 0) : d53373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d53373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2094, d53373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2097 q = 0) : d53376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro565 q selected
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2098 q = 0) : d53377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2099 q = 0) : d53378 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, d53378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2099, d53378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2100 q = 0) : d53379 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2100, d53379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2100, d53379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2126 q = 0) : d53405 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2126, d53405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2126, d53405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro2206 (p : Pattern) (selected : d2128 p = 0) : d53407 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2097 q = 0) : d53376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro565 q selected
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2098 q = 0) : d53377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2103 q = 0) : d53382 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d53382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2103, d53382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2104 q = 0) : d53383 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, d53383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2104, d53383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2128 q = 0) : d53407 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2128, d53407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2128, d53407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro2207 (p : Pattern) (selected : d2135 p = 0) : d53414 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2093 q = 0) : d53372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro564 q selected
    | true =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2094 q = 0) : d53373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d53373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2094, d53373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2097 q = 0) : d53376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro565 q selected
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2098 q = 0) : d53377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2099 q = 0) : d53378 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, d53378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2099, d53378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2134 q = 0) : d53413 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2134, d53413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2134, d53413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2135 q = 0) : d53414 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2135, d53414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2135, d53414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro2208 (p : Pattern) (selected : d2138 p = 0) : d53417 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2097 q = 0) : d53376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro565 q selected
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2098 q = 0) : d53377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2103 q = 0) : d53382 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d53382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2103, d53382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2137 q = 0) : d53416 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2137, d53416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2137, d53416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2138 q = 0) : d53417 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2138, d53417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2138, d53417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro2209 (p : Pattern) (selected : d2160 p = 0) : d53439 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2156 q = 0) : d53435 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2156, d53435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro578 q selected
    | true =>
      simp only [d2156, d53435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2157 q = 0) : d53436 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2157, d53436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2157, d53436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2093 q = 0) : d53372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro564 q selected
    | true =>
      simp only [d2093, d53372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2094 q = 0) : d53373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d53373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2094, d53373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2158 q = 0) : d53437 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2158, d53437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2158, d53437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2159 q = 0) : d53438 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2159, d53438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2159, d53438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2160 q = 0) : d53439 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2160, d53439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2160, d53439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro2210 (p : Pattern) (selected : d2267 p = 0) : d53380 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2259 q = 0) : d53372 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2259, d53372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro598 q selected
    | true =>
      simp only [d2259, d53372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2260 q = 0) : d53373 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2260, d53373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2260, d53373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2263 q = 0) : d53376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2263, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro599 q selected
    | true =>
      simp only [d2263, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2264 q = 0) : d53377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2264, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2264, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2265 q = 0) : d53378 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2265, d53378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2265, d53378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2266 q = 0) : d53379 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2266, d53379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2266, d53379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2267 q = 0) : d53380 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2267, d53380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2267, d53380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro2211 (p : Pattern) (selected : d2271 p = 0) : d53384 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2263 q = 0) : d53376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2263, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro599 q selected
    | true =>
      simp only [d2263, d53376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2264 q = 0) : d53377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2264, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2264, d53377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2269 q = 0) : d53382 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2269, d53382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2269, d53382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2270 q = 0) : d53383 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2270, d53383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2270, d53383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2271 q = 0) : d53384 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2271, d53384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2271, d53384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro2212 (p : Pattern) (selected : d63218 p = 0) : d63556 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d63204 q = 0) : d63543 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63204, d63543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2205 q selected
    | true =>
      simp only [d63204, d63543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2206 q selected
  have h2 (q : Pattern) (selected : d63205 q = 0) : d63544 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d63205, d63544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63205, d63544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d63206 q = 0) : d63545 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d63206, d63545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d63206, d63545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d63207 q = 0) : d63546 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d63207, d63546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63207, d63546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d63208 q = 0) : d63547 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63208, d63547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2207 q selected
    | true =>
      simp only [d63208, d63547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2208 q selected
  have h6 (q : Pattern) (selected : d63209 q = 0) : d63548 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d63209, d63548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63209, d63548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d63210 q = 0) : d63549 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d63210, d63549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d63210, d63549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d63211 q = 0) : d63550 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63211, d63550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2209 q selected
    | true =>
      simp only [d63211, d63550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2202 q selected
  have h9 (q : Pattern) (selected : d63212 q = 0) : d63535 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63212, d63535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2210 q selected
    | true =>
      simp only [d63212, d63535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2211 q selected
  have h10 (q : Pattern) (selected : d63213 q = 0) : d63551 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d63213, d63551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d63213, d63551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d63214 q = 0) : d63552 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63214, d63552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2202 q selected
    | true =>
      simp only [d63214, d63552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d63215 q = 0) : d63553 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d63215, d63553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d63215, d63553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d63216 q = 0) : d63554 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d63216, d63554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d63216, d63554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d63217 q = 0) : d63555 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d63217, d63555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d63217, d63555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d63218 q = 0) : d63556 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d63218, d63556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d63218, d63556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro2213 (p : Pattern) (selected : d63224 p = 0) : d63562 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d63220 q = 0) : d63558 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63220, d63558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2203 q selected
    | true =>
      simp only [d63220, d63558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d63221 q = 0) : d63559 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d63221, d63559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63221, d63559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d63222 q = 0) : d63560 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d63222, d63560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d63222, d63560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d63223 q = 0) : d63561 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d63223, d63561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63223, d63561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d63224 q = 0) : d63562 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d63224, d63562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63224, d63562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro2214 (p : Pattern) (selected : d63230 p = 0) : d63568 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d63201 q = 0) : d63540 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d63201, d63540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63201, d63540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2204 q selected
  have h2 (q : Pattern) (selected : d63202 q = 0) : d63541 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d63202, d63541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d63202, d63541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d63203 q = 0) : d63542 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63203, d63542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63203, d63542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d63219 q = 0) : d63557 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d63219, d63557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63219, d63557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2212 q selected
  have h5 (q : Pattern) (selected : d63225 q = 0) : d63563 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d63225, d63563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2204 q selected
    | true =>
      simp only [d63225, d63563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2213 q selected
  have h6 (q : Pattern) (selected : d63226 q = 0) : d63564 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d63226, d63564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d63226, d63564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d63227 q = 0) : d63565 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63227, d63565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d63227, d63565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d63228 q = 0) : d63566 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d63228, d63566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d63228, d63566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d63229 q = 0) : d63567 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d63229, d63567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d63229, d63567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d63230 q = 0) : d63568 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d63230, d63568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d63230, d63568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro2215 (p : Pattern) (selected : d63236 p = 0) : d63574 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d63231 q = 0) : d63569 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d63231, d63569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63231, d63569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2214 q selected
  have h2 (q : Pattern) (selected : d63232 q = 0) : d63570 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d63232, d63570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63232, d63570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d63233 q = 0) : d63571 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d63233, d63571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63233, d63571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d63234 q = 0) : d63572 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d63234, d63572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63234, d63572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d63235 q = 0) : d63573 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d63235, d63573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63235, d63573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d63236 q = 0) : d63574 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d63236, d63574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63236, d63574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2216 (p : Pattern) (selected : d63242 p = 0) : d63580 p = 1 := by
  have h0 (q : Pattern) (selected : d63063 q = 0) : d63405 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d63063, d63405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2145 q selected
    | true =>
      simp only [d63063, d63405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2159 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d63105 q = 0) : d63446 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d63105, d63446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d63105, d63446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2173 q selected
  have h3 (q : Pattern) (selected : d63106 q = 0) : d63447 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d63106, d63447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63106, d63447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d63148 q = 0) : d63488 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d63148, d63488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d63148, d63488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2187 q selected
  have h5 (q : Pattern) (selected : d63149 q = 0) : d63489 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d63149, d63489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d63149, d63489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d63150 q = 0) : d63490 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d63150, d63490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d63150, d63490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d63192 q = 0) : d63531 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d63192, d63531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d63192, d63531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2201 q selected
  have h8 (q : Pattern) (selected : d63193 q = 0) : d63532 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d63193, d63532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d63193, d63532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d63194 q = 0) : d63533 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d63194, d63533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d63194, d63533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d63195 q = 0) : d63534 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d63195, d63534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d63195, d63534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d63237 q = 0) : d63575 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d63237, d63575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d63237, d63575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2215 q selected
  have h12 (q : Pattern) (selected : d63238 q = 0) : d63576 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d63238, d63576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d63238, d63576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d63239 q = 0) : d63577 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d63239, d63577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d63239, d63577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d63240 q = 0) : d63578 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d63240, d63578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d63240, d63578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d63241 q = 0) : d63579 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d63241, d63579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d63241, d63579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d63242 q = 0) : d63580 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d63242, d63580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d63242, d63580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro2217 (p : Pattern) (selected : d63248 p = 0) : d63586 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d63243 q = 0) : d63581 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d63243, d63581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2216 q selected
    | true =>
      simp only [d63243, d63581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d63244 q = 0) : d63582 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d63244, d63582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d63244, d63582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d63245 q = 0) : d63583 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d63245, d63583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d63245, d63583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d63246 q = 0) : d63584 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d63246, d63584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d63246, d63584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d63247 q = 0) : d63585 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d63247, d63585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d63247, d63585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d63248 q = 0) : d63586 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d63248, d63586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d63248, d63586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2218 (p : Pattern) (selected : d63254 p = 0) : d63592 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d63249 q = 0) : d63587 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d63249, d63587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2217 q selected
    | true =>
      simp only [d63249, d63587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d63250 q = 0) : d63588 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d63250, d63588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d63250, d63588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d63251 q = 0) : d63589 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d63251, d63589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d63251, d63589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d63252 q = 0) : d63590 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d63252, d63590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d63252, d63590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d63253 q = 0) : d63591 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d63253, d63591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d63253, d63591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d63254 q = 0) : d63592 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d63254, d63592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d63254, d63592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2219 (p : Pattern) (selected : d63260 p = 0) : d63598 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d63255 q = 0) : d63593 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d63255, d63593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2218 q selected
    | true =>
      simp only [d63255, d63593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d63256 q = 0) : d63594 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d63256, d63594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d63256, d63594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d63257 q = 0) : d63595 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d63257, d63595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d63257, d63595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d63258 q = 0) : d63596 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d63258, d63596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d63258, d63596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d63259 q = 0) : d63597 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d63259, d63597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d63259, d63597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d63260 q = 0) : d63598 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d63260, d63598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d63260, d63598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2220 (p : Pattern) (selected : d63266 p = 0) : d63604 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d63261 q = 0) : d63599 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d63261, d63599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2219 q selected
    | true =>
      simp only [d63261, d63599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d63262 q = 0) : d63600 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d63262, d63600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d63262, d63600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d63263 q = 0) : d63601 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d63263, d63601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d63263, d63601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d63264 q = 0) : d63602 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d63264, d63602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d63264, d63602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d63265 q = 0) : d63603 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d63265, d63603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d63265, d63603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d63266 q = 0) : d63604 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d63266, d63604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d63266, d63604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2221 (p : Pattern) (selected : d63272 p = 0) : d63610 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d63267 q = 0) : d63605 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d63267, d63605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2220 q selected
    | true =>
      simp only [d63267, d63605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d63268 q = 0) : d63606 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d63268, d63606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d63268, d63606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d63269 q = 0) : d63607 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d63269, d63607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d63269, d63607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d63270 q = 0) : d63608 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d63270, d63608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d63270, d63608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d63271 q = 0) : d63609 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d63271, d63609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d63271, d63609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d63272 q = 0) : d63610 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d63272, d63610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d63272, d63610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2222 (p : Pattern) (selected : d63278 p = 0) : d63616 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d63273 q = 0) : d63611 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d63273, d63611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2221 q selected
    | true =>
      simp only [d63273, d63611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d63274 q = 0) : d63612 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d63274, d63612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d63274, d63612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d63275 q = 0) : d63613 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d63275, d63613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d63275, d63613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d63276 q = 0) : d63614 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d63276, d63614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d63276, d63614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d63277 q = 0) : d63615 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d63277, d63615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d63277, d63615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d63278 q = 0) : d63616 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d63278, d63616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d63278, d63616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2223 (p : Pattern) (selected : d63284 p = 0) : d63622 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d63279 q = 0) : d63617 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d63279, d63617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2222 q selected
    | true =>
      simp only [d63279, d63617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d63280 q = 0) : d63618 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d63280, d63618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d63280, d63618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d63281 q = 0) : d63619 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d63281, d63619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d63281, d63619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d63282 q = 0) : d63620 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d63282, d63620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d63282, d63620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d63283 q = 0) : d63621 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d63283, d63621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d63283, d63621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d63284 q = 0) : d63622 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d63284, d63622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d63284, d63622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro2224 (p : Pattern) (selected : d186 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d182 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro3 q selected
    | true =>
      simp only [d182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d183 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d184 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d185 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d186 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro2225 (p : Pattern) (selected : d62974 p = 1) : d63908 p = 1 := by
  have h0 (q : Pattern) (selected : d62965 q = 1) : d62965 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d62968 q = 1) : d62968 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d62969 q = 1) : d62969 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d62970 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d62970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2224 q selected
    | true =>
      simp only [d62970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d62971 q = 1) : d63905 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d62971, d63905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d62971, d63905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d62941 q = 1) : d62941 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d62972 q = 1) : d63906 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d62972, d63906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d62972, d63906, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d62973 q = 1) : d63907 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d62973, d63907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d62973, d63907, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d62974 q = 1) : d63908 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d62974, d63908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d62974, d63908, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro2226 (p : Pattern) (selected : d62981 p = 1) : d63914 p = 1 := by
  have h0 (q : Pattern) (selected : d62961 q = 1) : d62961 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d62975 q = 1) : d63909 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d62975, d63909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d62975, d63909, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2225 q selected
  have h3 (q : Pattern) (selected : d62976 q = 1) : d62976 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d62977 q = 1) : d63910 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62977, d63910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d62977, d63910, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d62978 q = 1) : d63911 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d62978, d63911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d62978, d63911, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d62979 q = 1) : d63912 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d62979, d63912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d62979, d63912, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d62980 q = 1) : d63913 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d62980, d63913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d62980, d63913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d62981 q = 1) : d63914 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d62981, d63914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d62981, d63914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h8 p selected
theorem eqIntro2227 (p : Pattern) (selected : d366 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d362 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro17 q selected
    | true =>
      simp only [d362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d363 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
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
  have h5 (q : Pattern) (selected : d364 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d365 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d366 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro2228 (p : Pattern) (selected : d63008 p = 1) : d63923 p = 1 := by
  have h0 (q : Pattern) (selected : d62997 q = 1) : d62997 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d63000 q = 1) : d63000 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d63001 q = 1) : d63001 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d63002 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2227 q selected
    | true =>
      simp only [d63002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2224 q selected
  have h4 (q : Pattern) (selected : d63003 q = 1) : d63920 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d63003, d63920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d63003, d63920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d63005 q = 1) : d63005 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d63006 q = 1) : d63921 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d63006, d63921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d63006, d63921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d63007 q = 1) : d63922 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d63007, d63922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d63007, d63922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d63008 q = 1) : d63923 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d63008, d63923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63008, d63923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro2229 (p : Pattern) (selected : d63015 p = 1) : d63929 p = 1 := by
  have h0 (q : Pattern) (selected : d62993 q = 1) : d62993 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d63009 q = 1) : d63924 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d63009, d63924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d63009, d63924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2228 q selected
  have h3 (q : Pattern) (selected : d63010 q = 1) : d63010 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d63011 q = 1) : d63925 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d63011, d63925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d63011, d63925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d63012 q = 1) : d63926 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63012, d63926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d63012, d63926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d63013 q = 1) : d63927 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d63013, d63927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63013, d63927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d63014 q = 1) : d63928 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d63014, d63928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d63014, d63928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d63015 q = 1) : d63929 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d63015, d63929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d63015, d63929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h8 p selected
theorem eqIntro2230 (p : Pattern) (selected : d63021 p = 1) : d63935 p = 1 := by
  have h0 (q : Pattern) (selected : d62954 q = 1) : d62954 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d62982 q = 1) : d63915 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d62982, d63915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d62982, d63915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2226 q selected
  have h3 (q : Pattern) (selected : d62983 q = 1) : d63916 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d62983, d63916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d62983, d63916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d62984 q = 1) : d63917 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d62984, d63917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d62984, d63917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d62985 q = 1) : d63918 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d62985, d63918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d62985, d63918, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d62986 q = 1) : d63919 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d62986, d63919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d62986, d63919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d63016 q = 1) : d63930 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d63016, d63930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d63016, d63930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2229 q selected
  have h8 (q : Pattern) (selected : d63017 q = 1) : d63931 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d63017, d63931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d63017, d63931, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d63018 q = 1) : d63932 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d63018, d63932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d63018, d63932, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d63019 q = 1) : d63933 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d63019, d63933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d63019, d63933, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d63020 q = 1) : d63934 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d63020, d63934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d63020, d63934, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d63021 q = 1) : d63935 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d63021, d63935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d63021, d63935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro2231 (p : Pattern) (selected : d595 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d587 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro32 q selected
    | true =>
      simp only [d587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d588 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d591 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33 q selected
    | true =>
      simp only [d591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d592 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d593 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d594 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d595 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro2232 (p : Pattern) (selected : d599 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d591 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro33 q selected
    | true =>
      simp only [d591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d592 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d597 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d598 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d599 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro2233 (p : Pattern) (selected : d63044 p = 1) : d63939 p = 1 := by
  have h0 (q : Pattern) (selected : d63033 q = 1) : d63033 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d63036 q = 1) : d63036 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d63037 q = 1) : d63037 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d63038 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2231 q selected
    | true =>
      simp only [d63038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2232 q selected
  have h4 (q : Pattern) (selected : d63039 q = 1) : d63936 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d63039, d63936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d63039, d63936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d63041 q = 1) : d63041 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d63042 q = 1) : d63937 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d63042, d63937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d63042, d63937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d63043 q = 1) : d63938 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d63043, d63938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d63043, d63938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d63044 q = 1) : d63939 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d63044, d63939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63044, d63939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro2234 (p : Pattern) (selected : d63056 p = 1) : d63945 p = 1 := by
  have h0 (q : Pattern) (selected : d63029 q = 1) : d63029 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d63045 q = 1) : d63940 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d63045, d63940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d63045, d63940, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2233 q selected
  have h3 (q : Pattern) (selected : d63051 q = 1) : d63051 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d63052 q = 1) : d63941 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d63052, d63941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d63052, d63941, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d63053 q = 1) : d63942 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63053, d63942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d63053, d63942, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d63054 q = 1) : d63943 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d63054, d63943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63054, d63943, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d63055 q = 1) : d63944 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d63055, d63944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d63055, d63944, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d63056 q = 1) : d63945 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d63056, d63945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d63056, d63945, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h8 p selected
theorem eqIntro2235 (p : Pattern) (selected : d63062 p = 1) : d63951 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d63057 q = 1) : d63946 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d63057, d63946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63057, d63946, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2234 q selected
  have h2 (q : Pattern) (selected : d63058 q = 1) : d63947 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d63058, d63947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63058, d63947, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d63059 q = 1) : d63948 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d63059, d63948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63059, d63948, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d63060 q = 1) : d63949 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d63060, d63949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63060, d63949, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d63061 q = 1) : d63950 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d63061, d63950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63061, d63950, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d63062 q = 1) : d63951 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d63062, d63951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63062, d63951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2236 (p : Pattern) (selected : d901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d893 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro56 q selected
    | true =>
      simp only [d893, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d894 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d894, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d897 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro57 q selected
    | true =>
      simp only [d897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d898 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d899 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d899, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d900 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d900, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d901 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d901, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro2237 (p : Pattern) (selected : d905 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d897 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro57 q selected
    | true =>
      simp only [d897, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d898 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d898, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d903 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d903, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d904 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d904, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d905 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d905, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro2238 (p : Pattern) (selected : d63086 p = 1) : d63956 p = 1 := by
  have h0 (q : Pattern) (selected : d63075 q = 1) : d63075 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d63078 q = 1) : d63078 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d63079 q = 1) : d63079 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d63080 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2236 q selected
    | true =>
      simp only [d63080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2237 q selected
  have h4 (q : Pattern) (selected : d63081 q = 1) : d63953 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d63081, d63953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d63081, d63953, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d63083 q = 1) : d63083 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d63084 q = 1) : d63954 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d63084, d63954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d63084, d63954, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d63085 q = 1) : d63955 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d63085, d63955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d63085, d63955, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d63086 q = 1) : d63956 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d63086, d63956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63086, d63956, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro2239 (p : Pattern) (selected : d63098 p = 1) : d63962 p = 1 := by
  have h0 (q : Pattern) (selected : d63071 q = 1) : d63071 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d63087 q = 1) : d63957 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d63087, d63957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d63087, d63957, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2238 q selected
  have h3 (q : Pattern) (selected : d63093 q = 1) : d63093 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d63094 q = 1) : d63958 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d63094, d63958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d63094, d63958, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d63095 q = 1) : d63959 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63095, d63959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d63095, d63959, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d63096 q = 1) : d63960 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d63096, d63960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63096, d63960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d63097 q = 1) : d63961 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d63097, d63961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d63097, d63961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d63098 q = 1) : d63962 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d63098, d63962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d63098, d63962, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h8 p selected
theorem eqIntro2240 (p : Pattern) (selected : d63104 p = 1) : d63968 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d63099 q = 1) : d63963 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d63099, d63963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63099, d63963, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2239 q selected
  have h2 (q : Pattern) (selected : d63100 q = 1) : d63964 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d63100, d63964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63100, d63964, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d63101 q = 1) : d63965 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d63101, d63965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63101, d63965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d63102 q = 1) : d63966 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d63102, d63966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63102, d63966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d63103 q = 1) : d63967 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d63103, d63967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63103, d63967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d63104 q = 1) : d63968 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d63104, d63968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63104, d63968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2241 (p : Pattern) (selected : d1312 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1304 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro86 q selected
    | true =>
      simp only [d1304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1305 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1308 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro87 q selected
    | true =>
      simp only [d1308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1309 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1310 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1311 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1312 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro2242 (p : Pattern) (selected : d1316 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1308 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro87 q selected
    | true =>
      simp only [d1308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1309 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1314 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1315 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1316 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro2243 (p : Pattern) (selected : d63129 p = 1) : d63974 p = 1 := by
  have h0 (q : Pattern) (selected : d63118 q = 1) : d63118 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d63121 q = 1) : d63121 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d63122 q = 1) : d63122 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d63123 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2241 q selected
    | true =>
      simp only [d63123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2242 q selected
  have h4 (q : Pattern) (selected : d63124 q = 1) : d63971 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d63124, d63971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d63124, d63971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d63126 q = 1) : d63126 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d63127 q = 1) : d63972 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d63127, d63972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d63127, d63972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d63128 q = 1) : d63973 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d63128, d63973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d63128, d63973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d63129 q = 1) : d63974 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d63129, d63974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63129, d63974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro2244 (p : Pattern) (selected : d63141 p = 1) : d63980 p = 1 := by
  have h0 (q : Pattern) (selected : d63114 q = 1) : d63114 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d63130 q = 1) : d63975 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d63130, d63975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d63130, d63975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2243 q selected
  have h3 (q : Pattern) (selected : d63136 q = 1) : d63136 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d63137 q = 1) : d63976 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d63137, d63976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d63137, d63976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d63138 q = 1) : d63977 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63138, d63977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d63138, d63977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d63139 q = 1) : d63978 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d63139, d63978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63139, d63978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d63140 q = 1) : d63979 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d63140, d63979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d63140, d63979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d63141 q = 1) : d63980 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d63141, d63980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d63141, d63980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h8 p selected
theorem eqIntro2245 (p : Pattern) (selected : d63147 p = 1) : d63986 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d63142 q = 1) : d63981 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d63142, d63981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63142, d63981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2244 q selected
  have h2 (q : Pattern) (selected : d63143 q = 1) : d63982 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d63143, d63982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63143, d63982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d63144 q = 1) : d63983 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d63144, d63983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63144, d63983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d63145 q = 1) : d63984 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d63145, d63984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63145, d63984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d63146 q = 1) : d63985 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d63146, d63985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63146, d63985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d63147 q = 1) : d63986 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d63147, d63986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63147, d63986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro2246 (p : Pattern) (selected : d1789 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1781 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro122 q selected
    | true =>
      simp only [d1781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1782 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1785 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro123 q selected
    | true =>
      simp only [d1785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1786 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d1787 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1788 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1789 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro2247 (p : Pattern) (selected : d1793 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1785 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro123 q selected
    | true =>
      simp only [d1785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1786 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d1791 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1792 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1793 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro2248 (p : Pattern) (selected : d63173 p = 1) : d63993 p = 1 := by
  have h0 (q : Pattern) (selected : d63162 q = 1) : d63162 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d63165 q = 1) : d63165 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d63166 q = 1) : d63166 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d63167 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d63167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2246 q selected
    | true =>
      simp only [d63167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2247 q selected
  have h4 (q : Pattern) (selected : d63168 q = 1) : d63990 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d63168, d63990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d63168, d63990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d63170 q = 1) : d63170 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d63171 q = 1) : d63991 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d63171, d63991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d63171, d63991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d63172 q = 1) : d63992 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d63172, d63992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d63172, d63992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d63173 q = 1) : d63993 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d63173, d63993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63173, d63993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro2249 (p : Pattern) (selected : d63185 p = 1) : d63999 p = 1 := by
  have h0 (q : Pattern) (selected : d63158 q = 1) : d63158 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d63174 q = 1) : d63994 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d63174, d63994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d63174, d63994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2248 q selected
  have h3 (q : Pattern) (selected : d63180 q = 1) : d63180 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d63181 q = 1) : d63995 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d63181, d63995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d63181, d63995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d63182 q = 1) : d63996 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63182, d63996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d63182, d63996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d63183 q = 1) : d63997 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d63183, d63997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d63183, d63997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d63184 q = 1) : d63998 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d63184, d63998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d63184, d63998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d63185 q = 1) : d63999 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d63185, d63999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d63185, d63999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h8 p selected
end NetHack.Soko22Hazard87
