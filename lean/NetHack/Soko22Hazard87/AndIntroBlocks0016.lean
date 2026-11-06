import NetHack.Soko22Hazard87.AndIntroBlocks0015
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro4000 (p : Pattern) (ha : d53847 p = 1) (hb : d57572 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53842 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d53842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3999 q ha hb
    | true =>
      simp only [d53842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53843 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d53843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53844 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d53844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53845 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d53845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53846 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d53846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53847 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d53847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4001 (p : Pattern) (ha : d53853 p = 1) (hb : d67923 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53848 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d53848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4000 q ha hb
    | true =>
      simp only [d53848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53849 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d53849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53850 q = 1) (hb : d57572 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d53850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53851 q = 1) (hb : d67923 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d53851, d67923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53851, d67923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d67923 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d53852 q = 1) (hb : d67923 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d53852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53853 q = 1) (hb : d67923 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d53853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro4002 (p : Pattern) (ha : d53859 p = 1) (hb : d67924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d67923 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53854 q = 1) (hb : d67923 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d53854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4001 q ha hb
    | true =>
      simp only [d53854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53855 q = 1) (hb : d67923 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d53855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53856 q = 1) (hb : d67924 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d53856, d67924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53856, d67924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d67924 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53857 q = 1) (hb : d67924 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d53857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53858 q = 1) (hb : d67924 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d53858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d53859 q = 1) (hb : d67924 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d53859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro4003 (p : Pattern) (ha : d53865 p = 1) (hb : d67924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d67924 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53860 q = 1) (hb : d67924 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d53860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4002 q ha hb
    | true =>
      simp only [d53860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53861 q = 1) (hb : d67924 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d53861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53862 q = 1) (hb : d67924 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d53862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53863 q = 1) (hb : d67924 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d53863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53864 q = 1) (hb : d67924 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d53864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53865 q = 1) (hb : d67924 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d53865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4004 (p : Pattern) (ha : d104 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d43 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d100 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d100, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d101 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d104 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4005 (p : Pattern) (ha : d111 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d43 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d100 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d100, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d101 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d50 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d107 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d109 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d110 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d111 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro4006 (p : Pattern) (ha : d213 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d43 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d100 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d100, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d101 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d213 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro4007 (p : Pattern) (ha : d4349 p = 1) (hb : d68222 p = 1) : d67625 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4340 q = 1) (hb : d68221 q = 1) : d4340 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4341 q = 1) (hb : d68222 q = 1) : d67615 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d68222, d67615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4341, d68222, d67615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4342 q = 1) (hb : d68222 q = 1) : d67623 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4342, d67623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4342, d67623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4343 q = 1) (hb : d68222 q = 1) : d67624 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4343, d67624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4343, d67624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4349 q = 1) (hb : d68222 q = 1) : d67625 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4349, d67625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4349, d67625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4008 (p : Pattern) (ha : d4359 p = 1) (hb : d68222 p = 1) : d67634 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4355 q = 1) (hb : d68221 q = 1) : d4355 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d85 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4356 q = 1) (hb : d68222 q = 1) : d67631 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4356, d68222, d67631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4356, d68222, d67631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4357 q = 1) (hb : d68222 q = 1) : d67632 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4357, d67632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4357, d67632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4358 q = 1) (hb : d68222 q = 1) : d67633 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4358, d67633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4358, d67633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4359 q = 1) (hb : d68222 q = 1) : d67634 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4359, d67634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4359, d67634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4009 (p : Pattern) (ha : d51643 p = 1) (hb : d68222 p = 1) : d68542 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d117 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d118 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d118, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d119 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d124 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d125 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d126 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d126, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d4335 q = 1) (hb : d68221 q = 1) : d4335 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d44 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d4336 q = 1) (hb : d68222 q = 1) : d67611 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d68222, d67611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4336, d68222, d67611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d51641 q = 1) (hb : d68222 q = 1) : d68540 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d68540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51641, d68540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51642 q = 1) (hb : d68222 q = 1) : d68541 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d68541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51642, d68541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51643 q = 1) (hb : d68222 q = 1) : d68542 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51643, d68542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51643, d68542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro4010 (p : Pattern) (ha : d51646 p = 1) (hb : d68222 p = 1) : d68543 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d117 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d118 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d118, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d119 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d120 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d124 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d125 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d125, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d126 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d126, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d4335 q = 1) (hb : d68221 q = 1) : d4335 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d44 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d4336 q = 1) (hb : d68222 q = 1) : d67611 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d68222, d67611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4336, d68222, d67611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d51641 q = 1) (hb : d68222 q = 1) : d68540 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d68540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51641, d68540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51642 q = 1) (hb : d68222 q = 1) : d68541 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d68541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51642, d68541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d195 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d196 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d196, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d197 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d197, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d198 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d200 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d201 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d201, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d202 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d202, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h22 (q : Pattern) (ha : d4340 q = 1) (hb : d68221 q = 1) : d4340 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d51 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d4341 q = 1) (hb : d68222 q = 1) : d67615 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d68222, d67615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d4341, d68222, d67615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d51644 q = 1) (hb : d68222 q = 1) : d67623 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51644, d67623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d51644, d67623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d51645 q = 1) (hb : d68222 q = 1) : d67624 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51645, d67624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d51645, d67624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d51646 q = 1) (hb : d68222 q = 1) : d68543 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51646, d68543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d51646, d68543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro4011 (p : Pattern) (ha : d51652 p = 1) (hb : d68222 p = 1) : d68549 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4004 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4004 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4005 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51647 q = 1) (hb : d68222 q = 1) : d68544 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51647, d68544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4009 q ha hb
    | true =>
      simp only [d51647, d68544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4010 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4006 q ha hb
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d51648 q = 1) (hb : d68222 q = 1) : d68545 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51648, d68545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51648, d68545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51649 q = 1) (hb : d68222 q = 1) : d68546 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51649, d68546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51649, d68546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51650 q = 1) (hb : d68222 q = 1) : d68547 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51650, d68547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51650, d68547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4350 q = 1) (hb : d68222 q = 1) : d67626 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4350, d67626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4350, d67626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4007 q ha hb
  have h12 (q : Pattern) (ha : d4351 q = 1) (hb : d68222 q = 1) : d67627 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4351, d67627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4351, d67627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4352 q = 1) (hb : d68222 q = 1) : d67628 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4352, d67628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4352, d67628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d4353 q = 1) (hb : d68222 q = 1) : d67629 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4353, d67629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4353, d67629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d51651 q = 1) (hb : d68222 q = 1) : d68548 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51651, d68548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51651, d68548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d4360 q = 1) (hb : d68222 q = 1) : d67635 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4360, d67635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4360, d67635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4008 q ha hb
  have h17 (q : Pattern) (ha : d4361 q = 1) (hb : d68222 q = 1) : d67636 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4361, d67636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d4361, d67636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d4362 q = 1) (hb : d68222 q = 1) : d67637 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4362, d67637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d4362, d67637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d4363 q = 1) (hb : d68222 q = 1) : d67638 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4363, d67638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d4363, d67638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d4364 q = 1) (hb : d68222 q = 1) : d67639 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4364, d67639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4364, d67639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d51652 q = 1) (hb : d68222 q = 1) : d68549 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51652, d68549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d51652, d68549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro4012 (p : Pattern) (ha : d284 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d157 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d280, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d281 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d282 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d283 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d284 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4013 (p : Pattern) (ha : d291 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d157 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d280, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d281 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d282 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d283 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d204 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d287 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d287, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d288 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d288, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d289 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d290 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d291 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro4014 (p : Pattern) (ha : d397 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d157 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d280, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d281 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d282 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d283 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d43 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d100 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d100, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d101 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d101, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d102 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d103 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d397 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro4015 (p : Pattern) (ha : d406 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d50 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d107, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d108, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d110 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d406 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4016 (p : Pattern) (ha : d462 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d84 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d458 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d458, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d458, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d459 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d459, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d459, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d460 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d461 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d462 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4017 (p : Pattern) (ha : d4385 p = 1) (hb : d68222 p = 1) : d67660 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4376 q = 1) (hb : d68221 q = 1) : d4376 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d391 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4377 q = 1) (hb : d68222 q = 1) : d67650 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4377, d68222, d67650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4377, d68222, d67650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4378 q = 1) (hb : d68222 q = 1) : d67658 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4378, d67658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4378, d67658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4379 q = 1) (hb : d68222 q = 1) : d67659 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4379, d67659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4379, d67659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4385 q = 1) (hb : d68222 q = 1) : d67660 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4385, d67660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4385, d67660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4018 (p : Pattern) (ha : d4395 p = 1) (hb : d68222 p = 1) : d67669 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4391 q = 1) (hb : d68221 q = 1) : d4391 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d452 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4392 q = 1) (hb : d68222 q = 1) : d67666 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4392, d68222, d67666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4392, d68222, d67666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4393 q = 1) (hb : d68222 q = 1) : d67667 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4393, d67667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4393, d67667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4394 q = 1) (hb : d68222 q = 1) : d67668 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4394, d67668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4394, d67668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4395 q = 1) (hb : d68222 q = 1) : d67669 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4395, d67669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4395, d67669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4019 (p : Pattern) (ha : d51660 p = 1) (hb : d68222 p = 1) : d68557 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d297 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d298 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d298, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d299 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d299, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d300 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d304 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d305 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d306 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d4371 q = 1) (hb : d68221 q = 1) : d4371 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d371 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d4372 q = 1) (hb : d68222 q = 1) : d67646 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4372, d68222, d67646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4372, d68222, d67646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d51658 q = 1) (hb : d68222 q = 1) : d68555 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51658, d68555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51658, d68555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51659 q = 1) (hb : d68222 q = 1) : d68556 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51659, d68556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51659, d68556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51660 q = 1) (hb : d68222 q = 1) : d68557 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51660, d68557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51660, d68557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro4020 (p : Pattern) (ha : d51663 p = 1) (hb : d68222 p = 1) : d68558 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d297 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d298 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d298, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d299 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d299, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d300 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d304 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d305 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d305, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d306 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d4371 q = 1) (hb : d68221 q = 1) : d4371 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d371 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d4372 q = 1) (hb : d68222 q = 1) : d67646 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4372, d68222, d67646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4372, d68222, d67646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d51658 q = 1) (hb : d68222 q = 1) : d68555 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51658, d68555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51658, d68555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51659 q = 1) (hb : d68222 q = 1) : d68556 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51659, d68556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51659, d68556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d377 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d378 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d378, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d378, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d379 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d379, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d379, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d380 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d382 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d383 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d383, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d383, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d384 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d384, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d384, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h22 (q : Pattern) (ha : d4376 q = 1) (hb : d68221 q = 1) : d4376 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d391 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d4377 q = 1) (hb : d68222 q = 1) : d67650 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4377, d68222, d67650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d4377, d68222, d67650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d51661 q = 1) (hb : d68222 q = 1) : d67658 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51661, d67658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d51661, d67658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d51662 q = 1) (hb : d68222 q = 1) : d67659 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51662, d67659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d51662, d67659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d51663 q = 1) (hb : d68222 q = 1) : d68558 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51663, d68558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d51663, d68558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro4021 (p : Pattern) (ha : d51676 p = 1) (hb : d68222 p = 1) : d68571 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4012 q ha hb
  have h2 (q : Pattern) (ha : d286 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d292 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4012 q ha hb
    | true =>
      simp only [d292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4013 q ha hb
  have h4 (q : Pattern) (ha : d293 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d294 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51664 q = 1) (hb : d68222 q = 1) : d68559 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51664, d68559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4019 q ha hb
    | true =>
      simp only [d51664, d68559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4020 q ha hb
  have h7 (q : Pattern) (ha : d398 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4014 q ha hb
    | true =>
      simp only [d398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4005 q ha hb
  have h8 (q : Pattern) (ha : d51665 q = 1) (hb : d68222 q = 1) : d68560 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51665, d68560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51665, d68560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51666 q = 1) (hb : d68222 q = 1) : d68561 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51666, d68561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51666, d68561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51667 q = 1) (hb : d68222 q = 1) : d68562 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51667, d68562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51667, d68562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4386 q = 1) (hb : d68222 q = 1) : d67661 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4386, d67661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4386, d67661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4017 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4015 q ha hb
  have h13 (q : Pattern) (ha : d51668 q = 1) (hb : d68222 q = 1) : d68563 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51668, d68563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51668, d68563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51669 q = 1) (hb : d68222 q = 1) : d68564 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51669, d68564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d51669, d68564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d51670 q = 1) (hb : d68222 q = 1) : d68565 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51670, d68565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d51670, d68565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d51671 q = 1) (hb : d68222 q = 1) : d68566 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51671, d68566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51671, d68566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d4396 q = 1) (hb : d68222 q = 1) : d67670 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4396, d67670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4396, d67670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4018 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4016 q ha hb
  have h19 (q : Pattern) (ha : d51672 q = 1) (hb : d68222 q = 1) : d68567 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51672, d68567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d51672, d68567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d51673 q = 1) (hb : d68222 q = 1) : d68568 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51673, d68568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d51673, d68568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d51674 q = 1) (hb : d68222 q = 1) : d68569 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51674, d68569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d51674, d68569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d51675 q = 1) (hb : d68222 q = 1) : d68570 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51675, d68570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d51675, d68570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d51676 q = 1) (hb : d68222 q = 1) : d68571 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51676, d68571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d51676, d68571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro4022 (p : Pattern) (ha : d51682 p = 1) (hb : d68222 p = 1) : d68577 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d68222 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51653 q = 1) (hb : d68222 q = 1) : d68550 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51653, d68550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51653, d68550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4011 q ha hb
  have h3 (q : Pattern) (ha : d51654 q = 1) (hb : d68222 q = 1) : d68551 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51654, d68551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51654, d68551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51655 q = 1) (hb : d68222 q = 1) : d68552 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51655, d68552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51655, d68552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51656 q = 1) (hb : d68222 q = 1) : d68553 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51656, d68553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51656, d68553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51657 q = 1) (hb : d68222 q = 1) : d68554 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51657, d68554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51657, d68554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51677 q = 1) (hb : d68222 q = 1) : d68572 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51677, d68572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51677, d68572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4021 q ha hb
  have h8 (q : Pattern) (ha : d51678 q = 1) (hb : d68222 q = 1) : d68573 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51678, d68573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51678, d68573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51679 q = 1) (hb : d68222 q = 1) : d68574 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51679, d68574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51679, d68574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d51680 q = 1) (hb : d68222 q = 1) : d68575 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51680, d68575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51680, d68575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d51681 q = 1) (hb : d68222 q = 1) : d68576 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51681, d68576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51681, d68576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d51682 q = 1) (hb : d68222 q = 1) : d68577 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d51682, d68577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51682, d68577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro4023 (p : Pattern) (ha : d497 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d492 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d493 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d493, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d494 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d494, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d495 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d496 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d497 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4024 (p : Pattern) (ha : d507 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d492 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d493 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d493, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d494 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d494, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d495 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d496 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d502 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d503 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d503, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d503, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d504 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d504, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d504, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d505 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d506 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d507 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro4025 (p : Pattern) (ha : d638 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d492 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d493 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d493, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d494 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d494, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d495 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d496 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d633 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d634 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d634, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d635 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d635, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d636 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d637 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d638 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro4026 (p : Pattern) (ha : d644 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d633 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d634 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d634, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d635 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d635, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d636 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d637 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d639 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d640 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d640, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d641 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d641, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d642 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d643 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d644 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro4027 (p : Pattern) (ha : d653 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d639 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d640 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d640, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d641 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d641, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d642 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d643 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d653 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4028 (p : Pattern) (ha : d736 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d731 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d732 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d732, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d732, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d733 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d733, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d733, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d734 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d735 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d736 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4029 (p : Pattern) (ha : d4422 p = 1) (hb : d68222 p = 1) : d67696 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4413 q = 1) (hb : d68221 q = 1) : d4413 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d627 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4414 q = 1) (hb : d68222 q = 1) : d67686 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4414, d68222, d67686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4414, d68222, d67686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4415 q = 1) (hb : d68222 q = 1) : d67694 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4415, d67694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4415, d67694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4416 q = 1) (hb : d68222 q = 1) : d67695 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4416, d67695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4416, d67695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4422 q = 1) (hb : d68222 q = 1) : d67696 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4422, d67696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4422, d67696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4030 (p : Pattern) (ha : d4432 p = 1) (hb : d68222 p = 1) : d67705 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4428 q = 1) (hb : d68221 q = 1) : d4428 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d721 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4429 q = 1) (hb : d68222 q = 1) : d67702 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4429, d68222, d67702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4429, d68222, d67702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4430 q = 1) (hb : d68222 q = 1) : d67703 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4430, d67703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4430, d67703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4431 q = 1) (hb : d68222 q = 1) : d67704 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4431, d67704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4431, d67704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4432 q = 1) (hb : d68222 q = 1) : d67705 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4432, d67705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4432, d67705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4031 (p : Pattern) (ha : d51685 p = 1) (hb : d68222 p = 1) : d68580 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d515 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d516 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d516, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d516, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d517 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d517, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d517, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d518 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d525 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d526 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d526, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d526, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d527 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d527, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d527, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d4408 q = 1) (hb : d68221 q = 1) : d4408 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d604 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d4409 q = 1) (hb : d68222 q = 1) : d67682 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4409, d68222, d67682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4409, d68222, d67682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d51683 q = 1) (hb : d68222 q = 1) : d68578 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51683, d68578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51683, d68578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51684 q = 1) (hb : d68222 q = 1) : d68579 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51684, d68579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51684, d68579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51685 q = 1) (hb : d68222 q = 1) : d68580 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51685, d68580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51685, d68580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro4032 (p : Pattern) (ha : d51688 p = 1) (hb : d68222 p = 1) : d68581 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d515 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d516 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d516, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d516, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d517 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d517, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d517, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d518 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d525 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d526 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d526, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d526, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d527 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d527, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d527, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d4408 q = 1) (hb : d68221 q = 1) : d4408 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d604 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d4409 q = 1) (hb : d68222 q = 1) : d67682 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4409, d68222, d67682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4409, d68222, d67682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d51683 q = 1) (hb : d68222 q = 1) : d68578 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51683, d68578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51683, d68578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51684 q = 1) (hb : d68222 q = 1) : d68579 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51684, d68579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51684, d68579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d611 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d612 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d612, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d612, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d613 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d613, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d613, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d614 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d617 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d618 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d618, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d618, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d619 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d619, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d619, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h22 (q : Pattern) (ha : d4413 q = 1) (hb : d68221 q = 1) : d4413 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d627 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d4414 q = 1) (hb : d68222 q = 1) : d67686 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4414, d68222, d67686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d4414, d68222, d67686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d51686 q = 1) (hb : d68222 q = 1) : d67694 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51686, d67694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d51686, d67694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d51687 q = 1) (hb : d68222 q = 1) : d67695 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51687, d67695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d51687, d67695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d51688 q = 1) (hb : d68222 q = 1) : d68581 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51688, d68581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d51688, d68581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro4033 (p : Pattern) (ha : d51701 p = 1) (hb : d68222 p = 1) : d68594 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d498 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4023 q ha hb
  have h2 (q : Pattern) (ha : d499 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d508 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4023 q ha hb
    | true =>
      simp only [d508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4024 q ha hb
  have h4 (q : Pattern) (ha : d509 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d510 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51689 q = 1) (hb : d68222 q = 1) : d68582 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51689, d68582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4031 q ha hb
    | true =>
      simp only [d51689, d68582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4032 q ha hb
  have h7 (q : Pattern) (ha : d645 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4025 q ha hb
    | true =>
      simp only [d645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4026 q ha hb
  have h8 (q : Pattern) (ha : d51690 q = 1) (hb : d68222 q = 1) : d68583 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51690, d68583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51690, d68583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51691 q = 1) (hb : d68222 q = 1) : d68584 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51691, d68584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51691, d68584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51692 q = 1) (hb : d68222 q = 1) : d68585 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51692, d68585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51692, d68585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4423 q = 1) (hb : d68222 q = 1) : d67697 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4423, d67697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4423, d67697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4029 q ha hb
  have h12 (q : Pattern) (ha : d654 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4027 q ha hb
  have h13 (q : Pattern) (ha : d51693 q = 1) (hb : d68222 q = 1) : d68586 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51693, d68586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51693, d68586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51694 q = 1) (hb : d68222 q = 1) : d68587 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51694, d68587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d51694, d68587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d51695 q = 1) (hb : d68222 q = 1) : d68588 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51695, d68588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d51695, d68588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d51696 q = 1) (hb : d68222 q = 1) : d68589 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51696, d68589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51696, d68589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d4433 q = 1) (hb : d68222 q = 1) : d67706 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4433, d67706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4433, d67706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4030 q ha hb
  have h18 (q : Pattern) (ha : d737 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4028 q ha hb
  have h19 (q : Pattern) (ha : d51697 q = 1) (hb : d68222 q = 1) : d68590 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51697, d68590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d51697, d68590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d51698 q = 1) (hb : d68222 q = 1) : d68591 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51698, d68591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d51698, d68591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d51699 q = 1) (hb : d68222 q = 1) : d68592 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51699, d68592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d51699, d68592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d51700 q = 1) (hb : d68222 q = 1) : d68593 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51700, d68593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d51700, d68593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d51701 q = 1) (hb : d68222 q = 1) : d68594 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51701, d68594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d51701, d68594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro4034 (p : Pattern) (ha : d51707 p = 1) (hb : d68222 p = 1) : d68600 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51702 q = 1) (hb : d68222 q = 1) : d68595 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51702, d68595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51702, d68595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4033 q ha hb
  have h2 (q : Pattern) (ha : d51703 q = 1) (hb : d68222 q = 1) : d68596 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51703, d68596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51703, d68596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d51704 q = 1) (hb : d68222 q = 1) : d68597 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51704, d68597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51704, d68597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51705 q = 1) (hb : d68222 q = 1) : d68598 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51705, d68598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51705, d68598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51706 q = 1) (hb : d68222 q = 1) : d68599 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51706, d68599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51706, d68599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51707 q = 1) (hb : d68222 q = 1) : d68600 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d51707, d68600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51707, d68600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4035 (p : Pattern) (ha : d789 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d784 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d785 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d785, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d786 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d786, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d787 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d788 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d789 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4036 (p : Pattern) (ha : d799 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d784 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d785 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d785, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d786 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d786, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d787 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d788 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d794 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d795 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d795, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d795, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d796 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d796, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d796, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d797 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d798 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d799 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro4037 (p : Pattern) (ha : d944 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d784 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d785 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d785, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d786 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d786, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d787 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d788 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d939 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d940 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d940, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d941 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d941, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d942 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d943 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d944 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro4038 (p : Pattern) (ha : d950 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d939 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d940 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d940, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d941 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d941, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d942 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d943 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d945 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d946 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d946, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d947 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d947, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d948 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d949 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d950 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro4039 (p : Pattern) (ha : d959 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d945 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d946 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d946, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d947 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d947, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d948 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d949 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d959 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4040 (p : Pattern) (ha : d1069 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1064 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1065 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1065, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1065, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1066 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1066, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1066, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1067 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1068 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1069 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4041 (p : Pattern) (ha : d4460 p = 1) (hb : d68222 p = 1) : d67733 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4451 q = 1) (hb : d68221 q = 1) : d4451 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d933 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4452 q = 1) (hb : d68222 q = 1) : d67723 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4452, d68222, d67723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4452, d68222, d67723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4453 q = 1) (hb : d68222 q = 1) : d67731 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4453, d67731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4453, d67731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4454 q = 1) (hb : d68222 q = 1) : d67732 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4454, d67732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4454, d67732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4460 q = 1) (hb : d68222 q = 1) : d67733 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4460, d67733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4460, d67733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4042 (p : Pattern) (ha : d4470 p = 1) (hb : d68222 p = 1) : d67742 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4466 q = 1) (hb : d68221 q = 1) : d4466 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1054 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4467 q = 1) (hb : d68222 q = 1) : d67739 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4467, d68222, d67739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4467, d68222, d67739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4468 q = 1) (hb : d68222 q = 1) : d67740 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4468, d67740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4468, d67740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4469 q = 1) (hb : d68222 q = 1) : d67741 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4469, d67741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4469, d67741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4470 q = 1) (hb : d68222 q = 1) : d67742 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4470, d67742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4470, d67742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4043 (p : Pattern) (ha : d51711 p = 1) (hb : d68222 p = 1) : d68604 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d807 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d808 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d808, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d808, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d809 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d809, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d809, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d810 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d817 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d818 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d818, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d818, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d819 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d819, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d819, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d4446 q = 1) (hb : d68221 q = 1) : d4446 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d910 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d4447 q = 1) (hb : d68222 q = 1) : d67719 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4447, d68222, d67719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4447, d68222, d67719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d51709 q = 1) (hb : d68222 q = 1) : d68602 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51709, d68602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51709, d68602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51710 q = 1) (hb : d68222 q = 1) : d68603 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51710, d68603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51710, d68603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51711 q = 1) (hb : d68222 q = 1) : d68604 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51711, d68604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51711, d68604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro4044 (p : Pattern) (ha : d51714 p = 1) (hb : d68222 p = 1) : d68605 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d807 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d808 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d808, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d808, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d809 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d809, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d809, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d810 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d817 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d818 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d818, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d818, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d819 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d819, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d819, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d4446 q = 1) (hb : d68221 q = 1) : d4446 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d910 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d4447 q = 1) (hb : d68222 q = 1) : d67719 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4447, d68222, d67719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4447, d68222, d67719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d51709 q = 1) (hb : d68222 q = 1) : d68602 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51709, d68602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51709, d68602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51710 q = 1) (hb : d68222 q = 1) : d68603 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51710, d68603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51710, d68603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d917 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d918 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d918, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d918, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d919 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d919, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d919, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d920 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d923 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d924 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d924, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d924, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d925 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d925, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d925, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h22 (q : Pattern) (ha : d4451 q = 1) (hb : d68221 q = 1) : d4451 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d933 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d4452 q = 1) (hb : d68222 q = 1) : d67723 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4452, d68222, d67723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d4452, d68222, d67723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d51712 q = 1) (hb : d68222 q = 1) : d67731 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51712, d67731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d51712, d67731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d51713 q = 1) (hb : d68222 q = 1) : d67732 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51713, d67732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d51713, d67732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d51714 q = 1) (hb : d68222 q = 1) : d68605 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51714, d68605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d51714, d68605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro4045 (p : Pattern) (ha : d51727 p = 1) (hb : d68222 p = 1) : d68618 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d790 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4035 q ha hb
  have h2 (q : Pattern) (ha : d791 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d800 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4035 q ha hb
    | true =>
      simp only [d800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4036 q ha hb
  have h4 (q : Pattern) (ha : d801 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d802 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51715 q = 1) (hb : d68222 q = 1) : d68606 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51715, d68606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4043 q ha hb
    | true =>
      simp only [d51715, d68606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4044 q ha hb
  have h7 (q : Pattern) (ha : d951 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4037 q ha hb
    | true =>
      simp only [d951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4038 q ha hb
  have h8 (q : Pattern) (ha : d51716 q = 1) (hb : d68222 q = 1) : d68607 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51716, d68607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51716, d68607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51717 q = 1) (hb : d68222 q = 1) : d68608 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51717, d68608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51717, d68608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51718 q = 1) (hb : d68222 q = 1) : d68609 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51718, d68609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51718, d68609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4461 q = 1) (hb : d68222 q = 1) : d67734 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4461, d67734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4461, d67734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4041 q ha hb
  have h12 (q : Pattern) (ha : d960 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4039 q ha hb
  have h13 (q : Pattern) (ha : d51719 q = 1) (hb : d68222 q = 1) : d68610 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51719, d68610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51719, d68610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51720 q = 1) (hb : d68222 q = 1) : d68611 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51720, d68611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d51720, d68611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d51721 q = 1) (hb : d68222 q = 1) : d68612 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51721, d68612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d51721, d68612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d51722 q = 1) (hb : d68222 q = 1) : d68613 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51722, d68613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51722, d68613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d4471 q = 1) (hb : d68222 q = 1) : d67743 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4471, d67743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4471, d67743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4042 q ha hb
  have h18 (q : Pattern) (ha : d1070 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4040 q ha hb
  have h19 (q : Pattern) (ha : d51723 q = 1) (hb : d68222 q = 1) : d68614 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51723, d68614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d51723, d68614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d51724 q = 1) (hb : d68222 q = 1) : d68615 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51724, d68615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d51724, d68615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d51725 q = 1) (hb : d68222 q = 1) : d68616 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51725, d68616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d51725, d68616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d51726 q = 1) (hb : d68222 q = 1) : d68617 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51726, d68617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d51726, d68617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d51727 q = 1) (hb : d68222 q = 1) : d68618 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51727, d68618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d51727, d68618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro4046 (p : Pattern) (ha : d51733 p = 1) (hb : d68222 p = 1) : d68624 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51728 q = 1) (hb : d68222 q = 1) : d68619 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51728, d68619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51728, d68619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4045 q ha hb
  have h2 (q : Pattern) (ha : d51729 q = 1) (hb : d68222 q = 1) : d68620 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51729, d68620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51729, d68620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d51730 q = 1) (hb : d68222 q = 1) : d68621 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51730, d68621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51730, d68621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51731 q = 1) (hb : d68222 q = 1) : d68622 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51731, d68622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51731, d68622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51732 q = 1) (hb : d68222 q = 1) : d68623 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51732, d68623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51732, d68623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51733 q = 1) (hb : d68222 q = 1) : d68624 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d51733, d68624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51733, d68624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4047 (p : Pattern) (ha : d1168 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1163 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1164 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1164, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1165 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1165, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1166 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1167 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1168 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4048 (p : Pattern) (ha : d1178 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1163 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1164 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1164, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1165 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1165, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1166 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1167 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1174 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1174, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1174, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d1175 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1175, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1175, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d1176 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1177 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1178 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro4049 (p : Pattern) (ha : d1355 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1163 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1164 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1164, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1165 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1165, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1166 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1167 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1350 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1351 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1351, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d1352 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1352, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d1353 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1354 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1355 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro4050 (p : Pattern) (ha : d1361 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1350 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1351 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1351, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1352 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1352, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1353 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1354 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1356 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1357 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1357, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1357, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d1358 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1358, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1358, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d1359 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1360 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1361 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro4051 (p : Pattern) (ha : d1370 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1356 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1357 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1357, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1357, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1358 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1358, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1358, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1359 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1360 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1370 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4052 (p : Pattern) (ha : d1503 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1498 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1499 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1499, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1499, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1500 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1500, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1500, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1501 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1502 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1503 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4053 (p : Pattern) (ha : d4499 p = 1) (hb : d68222 p = 1) : d67771 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4490 q = 1) (hb : d68221 q = 1) : d4490 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1344 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4491 q = 1) (hb : d68222 q = 1) : d67761 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4491, d68222, d67761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4491, d68222, d67761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4492 q = 1) (hb : d68222 q = 1) : d67769 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4492, d67769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4492, d67769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4493 q = 1) (hb : d68222 q = 1) : d67770 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4493, d67770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4493, d67770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4499 q = 1) (hb : d68222 q = 1) : d67771 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4499, d67771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4499, d67771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4054 (p : Pattern) (ha : d4509 p = 1) (hb : d68222 p = 1) : d67780 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4505 q = 1) (hb : d68221 q = 1) : d4505 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1488 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4506 q = 1) (hb : d68222 q = 1) : d67777 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4506, d68222, d67777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4506, d68222, d67777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4507 q = 1) (hb : d68222 q = 1) : d67778 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4507, d67778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4507, d67778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4508 q = 1) (hb : d68222 q = 1) : d67779 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4508, d67779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4508, d67779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4509 q = 1) (hb : d68222 q = 1) : d67780 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4509, d67780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4509, d67780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4055 (p : Pattern) (ha : d51738 p = 1) (hb : d68222 p = 1) : d68629 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1186 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1187 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1187, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1187, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1188 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1188, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1189 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1196 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1197 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1197, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1197, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1198 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1198, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d4485 q = 1) (hb : d68221 q = 1) : d4485 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d1321 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d4486 q = 1) (hb : d68222 q = 1) : d67757 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4486, d68222, d67757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4486, d68222, d67757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d51736 q = 1) (hb : d68222 q = 1) : d68627 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51736, d68627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51736, d68627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51737 q = 1) (hb : d68222 q = 1) : d68628 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51737, d68628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51737, d68628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51738 q = 1) (hb : d68222 q = 1) : d68629 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51738, d68629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51738, d68629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro4056 (p : Pattern) (ha : d51741 p = 1) (hb : d68222 p = 1) : d68630 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1186 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1187 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1187, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1187, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1188 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1188, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1189 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1196 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1197 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1197, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1197, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1198 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1198, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d4485 q = 1) (hb : d68221 q = 1) : d4485 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d1321 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d4486 q = 1) (hb : d68222 q = 1) : d67757 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4486, d68222, d67757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4486, d68222, d67757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d51736 q = 1) (hb : d68222 q = 1) : d68627 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51736, d68627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51736, d68627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51737 q = 1) (hb : d68222 q = 1) : d68628 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51737, d68628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51737, d68628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d1328 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d1329 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1329, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1329, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d1330 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1330, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d1330, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d1331 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d1334 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d1335 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1335, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1335, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d1336 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1336, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d1336, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h22 (q : Pattern) (ha : d4490 q = 1) (hb : d68221 q = 1) : d4490 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d1344 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d4491 q = 1) (hb : d68222 q = 1) : d67761 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4491, d68222, d67761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d4491, d68222, d67761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d51739 q = 1) (hb : d68222 q = 1) : d67769 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51739, d67769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d51739, d67769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d51740 q = 1) (hb : d68222 q = 1) : d67770 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51740, d67770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d51740, d67770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d51741 q = 1) (hb : d68222 q = 1) : d68630 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51741, d68630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d51741, d68630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro4057 (p : Pattern) (ha : d51754 p = 1) (hb : d68222 p = 1) : d68643 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1169 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4047 q ha hb
  have h2 (q : Pattern) (ha : d1170 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1179 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4047 q ha hb
    | true =>
      simp only [d1179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4048 q ha hb
  have h4 (q : Pattern) (ha : d1180 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1181 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51742 q = 1) (hb : d68222 q = 1) : d68631 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51742, d68631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4055 q ha hb
    | true =>
      simp only [d51742, d68631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4056 q ha hb
  have h7 (q : Pattern) (ha : d1362 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4049 q ha hb
    | true =>
      simp only [d1362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4050 q ha hb
  have h8 (q : Pattern) (ha : d51743 q = 1) (hb : d68222 q = 1) : d68632 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51743, d68632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51743, d68632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51744 q = 1) (hb : d68222 q = 1) : d68633 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51744, d68633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51744, d68633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51745 q = 1) (hb : d68222 q = 1) : d68634 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51745, d68634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51745, d68634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4500 q = 1) (hb : d68222 q = 1) : d67772 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4500, d67772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4500, d67772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4053 q ha hb
  have h12 (q : Pattern) (ha : d1371 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4051 q ha hb
  have h13 (q : Pattern) (ha : d51746 q = 1) (hb : d68222 q = 1) : d68635 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51746, d68635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51746, d68635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51747 q = 1) (hb : d68222 q = 1) : d68636 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51747, d68636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d51747, d68636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d51748 q = 1) (hb : d68222 q = 1) : d68637 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51748, d68637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d51748, d68637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d51749 q = 1) (hb : d68222 q = 1) : d68638 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51749, d68638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51749, d68638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d4510 q = 1) (hb : d68222 q = 1) : d67781 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4510, d67781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4510, d67781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4054 q ha hb
  have h18 (q : Pattern) (ha : d1504 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4052 q ha hb
  have h19 (q : Pattern) (ha : d51750 q = 1) (hb : d68222 q = 1) : d68639 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51750, d68639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d51750, d68639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d51751 q = 1) (hb : d68222 q = 1) : d68640 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51751, d68640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d51751, d68640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d51752 q = 1) (hb : d68222 q = 1) : d68641 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51752, d68641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d51752, d68641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d51753 q = 1) (hb : d68222 q = 1) : d68642 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51753, d68642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d51753, d68642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d51754 q = 1) (hb : d68222 q = 1) : d68643 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51754, d68643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d51754, d68643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro4058 (p : Pattern) (ha : d51760 p = 1) (hb : d68222 p = 1) : d68649 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51755 q = 1) (hb : d68222 q = 1) : d68644 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51755, d68644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51755, d68644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4057 q ha hb
  have h2 (q : Pattern) (ha : d51756 q = 1) (hb : d68222 q = 1) : d68645 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51756, d68645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51756, d68645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d51757 q = 1) (hb : d68222 q = 1) : d68646 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51757, d68646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51757, d68646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51758 q = 1) (hb : d68222 q = 1) : d68647 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51758, d68647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51758, d68647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51759 q = 1) (hb : d68222 q = 1) : d68648 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51759, d68648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51759, d68648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51760 q = 1) (hb : d68222 q = 1) : d68649 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d51760, d68649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51760, d68649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4059 (p : Pattern) (ha : d1629 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1624 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1625 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1625, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1626 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1626, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1627 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1628 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1629 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4060 (p : Pattern) (ha : d1639 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1624 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1625 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1625, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1626 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1626, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1627 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1628 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1634 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1635 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1635, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1635, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d1636 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1636, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1636, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d1637 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1638 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1639 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro4061 (p : Pattern) (ha : d1832 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1624 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1625 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1625, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1626 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1626, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1627 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1628 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1827 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1828 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1828, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d1829 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1829, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d1830 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1831 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1832 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro4062 (p : Pattern) (ha : d1838 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1827 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1828 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1828, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1829 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1829, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1830 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1831 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1833 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1834 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1834, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1834, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d1835 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1835, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1835, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d1836 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1837 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1838 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro4063 (p : Pattern) (ha : d1847 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1833 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1834 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1834, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1834, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1835 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1835, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1835, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1836 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1837 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1847 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4064 (p : Pattern) (ha : d1980 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1975 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1976 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1976, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1976, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1977 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1977, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1977, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1978 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1979 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1980 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4065 (p : Pattern) (ha : d4539 p = 1) (hb : d68222 p = 1) : d67810 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4530 q = 1) (hb : d68221 q = 1) : d4530 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1821 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4531 q = 1) (hb : d68222 q = 1) : d67800 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4531, d68222, d67800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4531, d68222, d67800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4532 q = 1) (hb : d68222 q = 1) : d67808 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4532, d67808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4532, d67808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4533 q = 1) (hb : d68222 q = 1) : d67809 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4533, d67809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4533, d67809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4539 q = 1) (hb : d68222 q = 1) : d67810 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4539, d67810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4539, d67810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4066 (p : Pattern) (ha : d4549 p = 1) (hb : d68222 p = 1) : d67819 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4545 q = 1) (hb : d68221 q = 1) : d4545 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1965 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4546 q = 1) (hb : d68222 q = 1) : d67816 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4546, d68222, d67816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4546, d68222, d67816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4547 q = 1) (hb : d68222 q = 1) : d67817 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4547, d67817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4547, d67817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4548 q = 1) (hb : d68222 q = 1) : d67818 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4548, d67818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4548, d67818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4549 q = 1) (hb : d68222 q = 1) : d67819 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4549, d67819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4549, d67819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4067 (p : Pattern) (ha : d51766 p = 1) (hb : d68222 p = 1) : d68655 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1647 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1648 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1648, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1648, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1649 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1649, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1650 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1657 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1658 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1658, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1658, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1659 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1659, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d4525 q = 1) (hb : d68221 q = 1) : d4525 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d1798 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d4526 q = 1) (hb : d68222 q = 1) : d67796 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4526, d68222, d67796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4526, d68222, d67796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d51764 q = 1) (hb : d68222 q = 1) : d68653 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51764, d68653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51764, d68653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51765 q = 1) (hb : d68222 q = 1) : d68654 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51765, d68654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51765, d68654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51766 q = 1) (hb : d68222 q = 1) : d68655 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51766, d68655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51766, d68655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro4068 (p : Pattern) (ha : d51769 p = 1) (hb : d68222 p = 1) : d68656 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1647 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1648 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1648, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1648, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1649 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1649, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1650 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1657 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1658 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1658, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1658, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1659 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1659, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d4525 q = 1) (hb : d68221 q = 1) : d4525 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d1798 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d4526 q = 1) (hb : d68222 q = 1) : d67796 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4526, d68222, d67796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4526, d68222, d67796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d51764 q = 1) (hb : d68222 q = 1) : d68653 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51764, d68653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51764, d68653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51765 q = 1) (hb : d68222 q = 1) : d68654 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51765, d68654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51765, d68654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d1805 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d1806 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1806, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1806, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d1807 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1807, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d1807, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d1808 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d1811 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d1812 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1812, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1812, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d1813 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1813, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d1813, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h22 (q : Pattern) (ha : d4530 q = 1) (hb : d68221 q = 1) : d4530 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d1821 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d4531 q = 1) (hb : d68222 q = 1) : d67800 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4531, d68222, d67800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d4531, d68222, d67800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d51767 q = 1) (hb : d68222 q = 1) : d67808 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51767, d67808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d51767, d67808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d51768 q = 1) (hb : d68222 q = 1) : d67809 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51768, d67809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d51768, d67809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d51769 q = 1) (hb : d68222 q = 1) : d68656 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51769, d68656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d51769, d68656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro4069 (p : Pattern) (ha : d51782 p = 1) (hb : d68222 p = 1) : d68669 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1630 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4059 q ha hb
  have h2 (q : Pattern) (ha : d1631 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1640 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4059 q ha hb
    | true =>
      simp only [d1640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4060 q ha hb
  have h4 (q : Pattern) (ha : d1641 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1642 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51770 q = 1) (hb : d68222 q = 1) : d68657 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51770, d68657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4067 q ha hb
    | true =>
      simp only [d51770, d68657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4068 q ha hb
  have h7 (q : Pattern) (ha : d1839 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4061 q ha hb
    | true =>
      simp only [d1839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4062 q ha hb
  have h8 (q : Pattern) (ha : d51771 q = 1) (hb : d68222 q = 1) : d68658 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51771, d68658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51771, d68658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51772 q = 1) (hb : d68222 q = 1) : d68659 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51772, d68659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51772, d68659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51773 q = 1) (hb : d68222 q = 1) : d68660 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51773, d68660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51773, d68660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4540 q = 1) (hb : d68222 q = 1) : d67811 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4540, d67811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4540, d67811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4065 q ha hb
  have h12 (q : Pattern) (ha : d1848 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4063 q ha hb
  have h13 (q : Pattern) (ha : d51774 q = 1) (hb : d68222 q = 1) : d68661 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51774, d68661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51774, d68661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51775 q = 1) (hb : d68222 q = 1) : d68662 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51775, d68662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d51775, d68662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d51776 q = 1) (hb : d68222 q = 1) : d68663 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51776, d68663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d51776, d68663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d51777 q = 1) (hb : d68222 q = 1) : d68664 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51777, d68664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51777, d68664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d4550 q = 1) (hb : d68222 q = 1) : d67820 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4550, d67820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4550, d67820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4066 q ha hb
  have h18 (q : Pattern) (ha : d1981 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4064 q ha hb
  have h19 (q : Pattern) (ha : d51778 q = 1) (hb : d68222 q = 1) : d68665 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51778, d68665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d51778, d68665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d51779 q = 1) (hb : d68222 q = 1) : d68666 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51779, d68666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d51779, d68666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d51780 q = 1) (hb : d68222 q = 1) : d68667 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51780, d68667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d51780, d68667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d51781 q = 1) (hb : d68222 q = 1) : d68668 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51781, d68668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d51781, d68668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d51782 q = 1) (hb : d68222 q = 1) : d68669 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51782, d68669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d51782, d68669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro4070 (p : Pattern) (ha : d51788 p = 1) (hb : d68222 p = 1) : d68675 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51783 q = 1) (hb : d68222 q = 1) : d68670 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51783, d68670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51783, d68670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4069 q ha hb
  have h2 (q : Pattern) (ha : d51784 q = 1) (hb : d68222 q = 1) : d68671 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51784, d68671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51784, d68671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d51785 q = 1) (hb : d68222 q = 1) : d68672 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51785, d68672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51785, d68672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51786 q = 1) (hb : d68222 q = 1) : d68673 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51786, d68673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51786, d68673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51787 q = 1) (hb : d68222 q = 1) : d68674 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51787, d68674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51787, d68674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51788 q = 1) (hb : d68222 q = 1) : d68675 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d51788, d68675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51788, d68675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4071 (p : Pattern) (ha : d2112 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2107 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2108 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2108, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2109 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2109, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2110 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2111 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2112 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4072 (p : Pattern) (ha : d2122 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2107 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2108 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2108, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2109 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2109, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2110 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2111 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d2117 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d2118 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2118, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2118, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d2119 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2119, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2119, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d2120 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2121 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d2122 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro4073 (p : Pattern) (ha : d2310 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2107 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2108 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2108, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2109 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2109, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2110 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2111 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d2305 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d2306 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2306, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d2307 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2307, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d2308 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2309 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d2310 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro4074 (p : Pattern) (ha : d2316 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2305 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2306 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2306, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2307 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2307, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2308 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2309 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d2311 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d2312 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2312, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2312, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d2313 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2313, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2313, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d2314 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2315 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d2316 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro4075 (p : Pattern) (ha : d2325 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2311 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2312 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2312, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2312, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2313 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2313, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2313, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2314 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2315 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2325 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4076 (p : Pattern) (ha : d2458 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2453 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2454 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2454, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2454, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2455 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2455, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2455, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2456 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2457 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2458 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4077 (p : Pattern) (ha : d4580 p = 1) (hb : d68222 p = 1) : d67850 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4571 q = 1) (hb : d68221 q = 1) : d4571 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2299 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4572 q = 1) (hb : d68222 q = 1) : d67840 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4572, d68222, d67840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4572, d68222, d67840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4573 q = 1) (hb : d68222 q = 1) : d67848 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4573, d67848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4573, d67848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4574 q = 1) (hb : d68222 q = 1) : d67849 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4574, d67849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4574, d67849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4580 q = 1) (hb : d68222 q = 1) : d67850 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4580, d67850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4580, d67850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4078 (p : Pattern) (ha : d4590 p = 1) (hb : d68222 p = 1) : d67859 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d4586 q = 1) (hb : d68221 q = 1) : d4586 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2443 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d4587 q = 1) (hb : d68222 q = 1) : d67856 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4587, d68222, d67856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4587, d68222, d67856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4588 q = 1) (hb : d68222 q = 1) : d67857 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4588, d67857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4588, d67857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4589 q = 1) (hb : d68222 q = 1) : d67858 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4589, d67858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4589, d67858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4590 q = 1) (hb : d68222 q = 1) : d67859 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4590, d67859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4590, d67859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4079 (p : Pattern) (ha : d51795 p = 1) (hb : d68222 p = 1) : d68682 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2130 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2131 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2131, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2131, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2132 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2132, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2133 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d2140 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2141 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2141, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2141, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d2142 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2142, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d4566 q = 1) (hb : d68221 q = 1) : d4566 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d2276 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d4567 q = 1) (hb : d68222 q = 1) : d67836 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4567, d68222, d67836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4567, d68222, d67836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d51793 q = 1) (hb : d68222 q = 1) : d68680 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51793, d68680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51793, d68680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51794 q = 1) (hb : d68222 q = 1) : d68681 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51794, d68681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51794, d68681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51795 q = 1) (hb : d68222 q = 1) : d68682 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51795, d68682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51795, d68682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro4080 (p : Pattern) (ha : d51798 p = 1) (hb : d68222 p = 1) : d68683 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2130 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2131 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2131, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2131, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2132 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2132, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2133 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d2140 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2141 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2141, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2141, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d2142 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2142, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d4566 q = 1) (hb : d68221 q = 1) : d4566 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d2276 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d4567 q = 1) (hb : d68222 q = 1) : d67836 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4567, d68222, d67836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4567, d68222, d67836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d51793 q = 1) (hb : d68222 q = 1) : d68680 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51793, d68680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51793, d68680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51794 q = 1) (hb : d68222 q = 1) : d68681 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51794, d68681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51794, d68681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d2283 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d2284 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2284, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2284, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d2285 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2285, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d2285, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d2286 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d2289 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d2290 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2290, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2290, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d2291 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2291, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d2291, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h22 (q : Pattern) (ha : d4571 q = 1) (hb : d68221 q = 1) : d4571 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d0 q = 1) (hb : d2299 q = 1) : d0 q = 1 := by
    exact ha
  have h24 (q : Pattern) (ha : d4572 q = 1) (hb : d68222 q = 1) : d67840 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4572, d68222, d67840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d4572, d68222, d67840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d51796 q = 1) (hb : d68222 q = 1) : d67848 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51796, d67848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d51796, d67848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d51797 q = 1) (hb : d68222 q = 1) : d67849 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51797, d67849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d51797, d67849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d51798 q = 1) (hb : d68222 q = 1) : d68683 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51798, d68683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d51798, d68683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro4081 (p : Pattern) (ha : d51811 p = 1) (hb : d68222 p = 1) : d68696 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2113 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4071 q ha hb
  have h2 (q : Pattern) (ha : d2114 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2123 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4071 q ha hb
    | true =>
      simp only [d2123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4072 q ha hb
  have h4 (q : Pattern) (ha : d2124 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2125 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51799 q = 1) (hb : d68222 q = 1) : d68684 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51799, d68684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4079 q ha hb
    | true =>
      simp only [d51799, d68684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4080 q ha hb
  have h7 (q : Pattern) (ha : d2317 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4073 q ha hb
    | true =>
      simp only [d2317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4074 q ha hb
  have h8 (q : Pattern) (ha : d51800 q = 1) (hb : d68222 q = 1) : d68685 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51800, d68685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51800, d68685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51801 q = 1) (hb : d68222 q = 1) : d68686 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51801, d68686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d51801, d68686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d51802 q = 1) (hb : d68222 q = 1) : d68687 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51802, d68687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51802, d68687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4581 q = 1) (hb : d68222 q = 1) : d67851 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4581, d67851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4581, d67851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4077 q ha hb
  have h12 (q : Pattern) (ha : d2326 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4075 q ha hb
  have h13 (q : Pattern) (ha : d51803 q = 1) (hb : d68222 q = 1) : d68688 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51803, d68688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51803, d68688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51804 q = 1) (hb : d68222 q = 1) : d68689 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51804, d68689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d51804, d68689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d51805 q = 1) (hb : d68222 q = 1) : d68690 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51805, d68690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d51805, d68690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d51806 q = 1) (hb : d68222 q = 1) : d68691 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51806, d68691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51806, d68691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d4591 q = 1) (hb : d68222 q = 1) : d67860 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4591, d67860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4591, d67860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4078 q ha hb
  have h18 (q : Pattern) (ha : d2459 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4076 q ha hb
  have h19 (q : Pattern) (ha : d51807 q = 1) (hb : d68222 q = 1) : d68692 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51807, d68692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d51807, d68692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d51808 q = 1) (hb : d68222 q = 1) : d68693 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51808, d68693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d51808, d68693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d51809 q = 1) (hb : d68222 q = 1) : d68694 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51809, d68694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d51809, d68694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d51810 q = 1) (hb : d68222 q = 1) : d68695 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51810, d68695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d51810, d68695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d51811 q = 1) (hb : d68222 q = 1) : d68696 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51811, d68696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d51811, d68696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro4082 (p : Pattern) (ha : d51817 p = 1) (hb : d68222 p = 1) : d68702 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51812 q = 1) (hb : d68222 q = 1) : d68697 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51812, d68697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51812, d68697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4081 q ha hb
  have h2 (q : Pattern) (ha : d51813 q = 1) (hb : d68222 q = 1) : d68698 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51813, d68698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51813, d68698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d51814 q = 1) (hb : d68222 q = 1) : d68699 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51814, d68699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51814, d68699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51815 q = 1) (hb : d68222 q = 1) : d68700 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51815, d68700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51815, d68700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51816 q = 1) (hb : d68222 q = 1) : d68701 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51816, d68701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51816, d68701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51817 q = 1) (hb : d68222 q = 1) : d68702 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d51817, d68702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51817, d68702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4083 (p : Pattern) (ha : d51823 p = 1) (hb : d68222 p = 1) : d68708 p = 1 := by
  have h0 (q : Pattern) (ha : d51708 q = 1) (hb : d68222 q = 1) : d68601 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d51708, d68601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4022 q ha hb
    | true =>
      simp only [d51708, d68601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4034 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51734 q = 1) (hb : d68222 q = 1) : d68625 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d51734, d68625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51734, d68625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4046 q ha hb
  have h3 (q : Pattern) (ha : d51735 q = 1) (hb : d68222 q = 1) : d68626 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d51735, d68626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51735, d68626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51761 q = 1) (hb : d68222 q = 1) : d68650 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d51761, d68650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51761, d68650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4058 q ha hb
  have h5 (q : Pattern) (ha : d51762 q = 1) (hb : d68222 q = 1) : d68651 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d51762, d68651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51762, d68651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51763 q = 1) (hb : d68222 q = 1) : d68652 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d51763, d68652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51763, d68652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51789 q = 1) (hb : d68222 q = 1) : d68676 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d51789, d68676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51789, d68676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4070 q ha hb
  have h8 (q : Pattern) (ha : d51790 q = 1) (hb : d68222 q = 1) : d68677 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d51790, d68677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51790, d68677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51791 q = 1) (hb : d68222 q = 1) : d68678 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d51791, d68678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51791, d68678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d51792 q = 1) (hb : d68222 q = 1) : d68679 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d51792, d68679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51792, d68679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d51818 q = 1) (hb : d68222 q = 1) : d68703 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d51818, d68703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51818, d68703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4082 q ha hb
  have h12 (q : Pattern) (ha : d51819 q = 1) (hb : d68222 q = 1) : d68704 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d51819, d68704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51819, d68704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d51820 q = 1) (hb : d68222 q = 1) : d68705 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d51820, d68705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51820, d68705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d51821 q = 1) (hb : d68222 q = 1) : d68706 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d51821, d68706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51821, d68706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d51822 q = 1) (hb : d68222 q = 1) : d68707 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d51822, d68707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51822, d68707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d51823 q = 1) (hb : d68222 q = 1) : d68708 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d51823, d68708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d51823, d68708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro4084 (p : Pattern) (ha : d51829 p = 1) (hb : d68222 p = 1) : d68714 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51824 q = 1) (hb : d68222 q = 1) : d68709 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d51824, d68709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4083 q ha hb
    | true =>
      simp only [d51824, d68709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51825 q = 1) (hb : d68222 q = 1) : d68710 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d51825, d68710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51825, d68710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d51826 q = 1) (hb : d68222 q = 1) : d68711 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d51826, d68711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51826, d68711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51827 q = 1) (hb : d68222 q = 1) : d68712 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d51827, d68712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51827, d68712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51828 q = 1) (hb : d68222 q = 1) : d68713 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d51828, d68713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51828, d68713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d51829 q = 1) (hb : d68222 q = 1) : d68714 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d51829, d68714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51829, d68714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4085 (p : Pattern) (ha : d51835 p = 1) (hb : d68222 p = 1) : d68720 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51830 q = 1) (hb : d68222 q = 1) : d68715 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d51830, d68715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4084 q ha hb
    | true =>
      simp only [d51830, d68715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51831 q = 1) (hb : d68222 q = 1) : d68716 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d51831, d68716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51831, d68716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d51832 q = 1) (hb : d68222 q = 1) : d68717 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d51832, d68717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51832, d68717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51833 q = 1) (hb : d68222 q = 1) : d68718 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d51833, d68718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51833, d68718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51834 q = 1) (hb : d68222 q = 1) : d68719 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d51834, d68719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51834, d68719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d51835 q = 1) (hb : d68222 q = 1) : d68720 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d51835, d68720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51835, d68720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4086 (p : Pattern) (ha : d51841 p = 1) (hb : d68222 p = 1) : d68726 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51836 q = 1) (hb : d68222 q = 1) : d68721 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d51836, d68721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4085 q ha hb
    | true =>
      simp only [d51836, d68721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51837 q = 1) (hb : d68222 q = 1) : d68722 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d51837, d68722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51837, d68722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d51838 q = 1) (hb : d68222 q = 1) : d68723 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d51838, d68723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51838, d68723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51839 q = 1) (hb : d68222 q = 1) : d68724 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d51839, d68724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51839, d68724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51840 q = 1) (hb : d68222 q = 1) : d68725 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d51840, d68725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51840, d68725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d51841 q = 1) (hb : d68222 q = 1) : d68726 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d51841, d68726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51841, d68726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4087 (p : Pattern) (ha : d51847 p = 1) (hb : d68222 p = 1) : d68732 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51842 q = 1) (hb : d68222 q = 1) : d68727 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d51842, d68727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4086 q ha hb
    | true =>
      simp only [d51842, d68727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51843 q = 1) (hb : d68222 q = 1) : d68728 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d51843, d68728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51843, d68728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d51844 q = 1) (hb : d68222 q = 1) : d68729 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d51844, d68729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51844, d68729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51845 q = 1) (hb : d68222 q = 1) : d68730 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d51845, d68730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51845, d68730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51846 q = 1) (hb : d68222 q = 1) : d68731 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d51846, d68731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51846, d68731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d51847 q = 1) (hb : d68222 q = 1) : d68732 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d51847, d68732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51847, d68732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4088 (p : Pattern) (ha : d51853 p = 1) (hb : d68222 p = 1) : d68738 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51848 q = 1) (hb : d68222 q = 1) : d68733 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d51848, d68733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4087 q ha hb
    | true =>
      simp only [d51848, d68733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51849 q = 1) (hb : d68222 q = 1) : d68734 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d51849, d68734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51849, d68734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d51850 q = 1) (hb : d68222 q = 1) : d68735 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d51850, d68735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51850, d68735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51851 q = 1) (hb : d68222 q = 1) : d68736 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d51851, d68736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51851, d68736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51852 q = 1) (hb : d68222 q = 1) : d68737 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d51852, d68737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51852, d68737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d51853 q = 1) (hb : d68222 q = 1) : d68738 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d51853, d68738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51853, d68738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4089 (p : Pattern) (ha : d51859 p = 1) (hb : d68223 p = 1) : d68744 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51854 q = 1) (hb : d68222 q = 1) : d68739 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d51854, d68739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4088 q ha hb
    | true =>
      simp only [d51854, d68739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51855 q = 1) (hb : d68222 q = 1) : d68740 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d51855, d68740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51855, d68740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d51856 q = 1) (hb : d68223 q = 1) : d68741 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d51856, d68223, d68741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51856, d68223, d68741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d68223 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d51857 q = 1) (hb : d68223 q = 1) : d68742 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d51857, d68742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51857, d68742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51858 q = 1) (hb : d68223 q = 1) : d68743 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d51858, d68743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51858, d68743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d51859 q = 1) (hb : d68223 q = 1) : d68744 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d51859, d68744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d51859, d68744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro4090 (p : Pattern) (ha : d51865 p = 1) (hb : d68223 p = 1) : d68750 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68223 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51860 q = 1) (hb : d68223 q = 1) : d68745 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d51860, d68745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4089 q ha hb
    | true =>
      simp only [d51860, d68745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d51861 q = 1) (hb : d68223 q = 1) : d68746 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d51861, d68746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51861, d68746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d51862 q = 1) (hb : d68223 q = 1) : d68747 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d51862, d68747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51862, d68747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51863 q = 1) (hb : d68223 q = 1) : d68748 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d51863, d68748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51863, d68748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51864 q = 1) (hb : d68223 q = 1) : d68749 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d51864, d68749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d51864, d68749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d51865 q = 1) (hb : d68223 q = 1) : d68750 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d51865, d68750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51865, d68750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4091 (p : Pattern) (ha : d67625 p = 1) (hb : d68238 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d204 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22 q ha hb
    | true =>
      simp only [d204, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h2 (q : Pattern) (ha : d4340 q = 1) (hb : d68229 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d68229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4340, d68229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d67615 q = 1) (hb : d68230 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67615, d68230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67615, d68230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d67623 q = 1) (hb : d68231 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67623, d68231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67623, d68231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67624 q = 1) (hb : d68232 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67624, d68232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67624, d68232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67625 q = 1) (hb : d68238 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67625, d68238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67625, d68238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4092 (p : Pattern) (ha : d67634 p = 1) (hb : d68248 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d244 q = 1) (hb : d52062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26 q ha hb
    | true =>
      simp only [d244, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
  have h2 (q : Pattern) (ha : d4355 q = 1) (hb : d68244 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4355, d68244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4355, d68244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51937 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d67631 q = 1) (hb : d68245 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67631, d68245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67631, d68245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d67632 q = 1) (hb : d68246 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67632, d68246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67632, d68246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67633 q = 1) (hb : d68247 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67633, d68247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67633, d68247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67634 q = 1) (hb : d68248 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67634, d68248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67634, d68248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4093 (p : Pattern) (ha : d68228 p = 1) (hb : d68542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d157 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
    | true =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h2 (q : Pattern) (ha : d4335 q = 1) (hb : d68224 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d68224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4335, d68224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d67611 q = 1) (hb : d68225 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67611, d68225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67611, d68225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68226 q = 1) (hb : d68540 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68226, d68540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68226, d68540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d68227 q = 1) (hb : d68541 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68227, d68541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68227, d68541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d68228 q = 1) (hb : d68542 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68228, d68542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68228, d68542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4094 (p : Pattern) (ha : d68233 p = 1) (hb : d68543 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d157 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
    | true =>
      simp only [d157, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h2 (q : Pattern) (ha : d4335 q = 1) (hb : d68224 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d68224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4335, d68224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d51896 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d67611 q = 1) (hb : d68225 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67611, d68225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67611, d68225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68226 q = 1) (hb : d68540 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68226, d68540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68226, d68540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d68227 q = 1) (hb : d68541 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68227, d68541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68227, d68541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d204 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22 q ha hb
    | true =>
      simp only [d204, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h8 (q : Pattern) (ha : d4340 q = 1) (hb : d68229 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d68229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4340, d68229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51903 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d67615 q = 1) (hb : d68230 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67615, d68230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d67615, d68230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d67623 q = 1) (hb : d68231 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67623, d68231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67623, d68231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d67624 q = 1) (hb : d68232 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67624, d68232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67624, d68232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d68233 q = 1) (hb : d68543 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68233, d68543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d68233, d68543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  exact h13 p ha hb
theorem andIntro4095 (p : Pattern) (ha : d68254 p = 1) (hb : d68549 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68234 q = 1) (hb : d68544 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68234, d68544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4093 q ha hb
    | true =>
      simp only [d68234, d68544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4094 q ha hb
  have h2 (q : Pattern) (ha : d68235 q = 1) (hb : d68545 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68235, d68545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68235, d68545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68236 q = 1) (hb : d68546 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68236, d68546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68236, d68546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68237 q = 1) (hb : d68547 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68237, d68547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68237, d68547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d67626 q = 1) (hb : d68239 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67626, d68239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67626, d68239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4091 q ha hb
  have h6 (q : Pattern) (ha : d67627 q = 1) (hb : d68240 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67627, d68240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d67627, d68240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d67628 q = 1) (hb : d68241 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67628, d68241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d67628, d68241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d67629 q = 1) (hb : d68242 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67629, d68242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d67629, d68242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d68243 q = 1) (hb : d68548 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68243, d68548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68243, d68548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d67635 q = 1) (hb : d68249 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67635, d68249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67635, d68249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4092 q ha hb
  have h11 (q : Pattern) (ha : d67636 q = 1) (hb : d68250 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d67636, d68250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d67636, d68250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d67637 q = 1) (hb : d68251 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d67637, d68251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d67637, d68251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d67638 q = 1) (hb : d68252 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d67638, d68252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d67638, d68252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d67639 q = 1) (hb : d68253 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d67639, d68253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d67639, d68253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d68254 q = 1) (hb : d68549 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d68254, d68549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68254, d68549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro4096 (p : Pattern) (ha : d67660 p = 1) (hb : d68274 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d386 q = 1) (hb : d52154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d386, d52154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45 q ha hb
    | true =>
      simp only [d386, d52154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22 q ha hb
  have h2 (q : Pattern) (ha : d4376 q = 1) (hb : d68265 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4376, d68265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4376, d68265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52157 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d67650 q = 1) (hb : d68266 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67650, d68266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67650, d68266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d67658 q = 1) (hb : d68267 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67658, d68267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67658, d68267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67659 q = 1) (hb : d68268 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67659, d68268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67659, d68268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67660 q = 1) (hb : d68274 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67660, d68274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67660, d68274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4097 (p : Pattern) (ha : d67669 p = 1) (hb : d68284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d430 q = 1) (hb : d52196 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d430, d52196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49 q ha hb
    | true =>
      simp only [d430, d52196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26 q ha hb
  have h2 (q : Pattern) (ha : d4391 q = 1) (hb : d68280 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4391, d68280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4391, d68280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52199 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d67666 q = 1) (hb : d68281 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67666, d68281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67666, d68281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d67667 q = 1) (hb : d68282 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67667, d68282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67667, d68282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67668 q = 1) (hb : d68283 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67668, d68283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67668, d68283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67669 q = 1) (hb : d68284 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67669, d68284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67669, d68284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4098 (p : Pattern) (ha : d68264 p = 1) (hb : d68557 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d337 q = 1) (hb : d52136 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d337, d52136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53 q ha hb
    | true =>
      simp only [d337, d52136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
  have h2 (q : Pattern) (ha : d4371 q = 1) (hb : d68260 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4371, d68260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4371, d68260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52139 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d67646 q = 1) (hb : d68261 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67646, d68261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67646, d68261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68262 q = 1) (hb : d68555 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68262, d68555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68262, d68555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d68263 q = 1) (hb : d68556 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68263, d68556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68263, d68556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d68264 q = 1) (hb : d68557 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68264, d68557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68264, d68557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4099 (p : Pattern) (ha : d68269 p = 1) (hb : d68558 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d337 q = 1) (hb : d52136 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d337, d52136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro53 q ha hb
    | true =>
      simp only [d337, d52136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30 q ha hb
  have h2 (q : Pattern) (ha : d4371 q = 1) (hb : d68260 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4371, d68260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4371, d68260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52139 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d67646 q = 1) (hb : d68261 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67646, d68261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67646, d68261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68262 q = 1) (hb : d68555 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68262, d68555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68262, d68555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d68263 q = 1) (hb : d68556 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68263, d68556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68263, d68556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d386 q = 1) (hb : d52154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d386, d52154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro45 q ha hb
    | true =>
      simp only [d386, d52154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro22 q ha hb
  have h8 (q : Pattern) (ha : d4376 q = 1) (hb : d68265 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4376, d68265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4376, d68265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52157 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d67650 q = 1) (hb : d68266 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67650, d68266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d67650, d68266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d67658 q = 1) (hb : d68267 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67658, d68267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67658, d68267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d67659 q = 1) (hb : d68268 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67659, d68268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67659, d68268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d68269 q = 1) (hb : d68558 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68269, d68558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d68269, d68558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  exact h13 p ha hb
theorem andIntro4100 (p : Pattern) (ha : d68290 p = 1) (hb : d68571 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68270 q = 1) (hb : d68559 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68270, d68559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4098 q ha hb
    | true =>
      simp only [d68270, d68559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4099 q ha hb
  have h2 (q : Pattern) (ha : d68271 q = 1) (hb : d68560 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68271, d68560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68271, d68560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68272 q = 1) (hb : d68561 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68272, d68561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68272, d68561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68273 q = 1) (hb : d68562 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68273, d68562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68273, d68562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d67661 q = 1) (hb : d68275 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67661, d68275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67661, d68275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4096 q ha hb
  have h6 (q : Pattern) (ha : d68276 q = 1) (hb : d68563 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68276, d68563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d68276, d68563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d68277 q = 1) (hb : d68564 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68277, d68564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d68277, d68564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d68278 q = 1) (hb : d68565 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68278, d68565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d68278, d68565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d68279 q = 1) (hb : d68566 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68279, d68566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68279, d68566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d67670 q = 1) (hb : d68285 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67670, d68285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67670, d68285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4097 q ha hb
  have h11 (q : Pattern) (ha : d68286 q = 1) (hb : d68567 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68286, d68567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d68286, d68567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d68287 q = 1) (hb : d68568 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68287, d68568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d68287, d68568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d68288 q = 1) (hb : d68569 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68288, d68569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d68288, d68569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d68289 q = 1) (hb : d68570 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68289, d68570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d68289, d68570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d68290 q = 1) (hb : d68571 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d68290, d68571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68290, d68571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro4101 (p : Pattern) (ha : d68296 p = 1) (hb : d68577 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d68255 q = 1) (hb : d68550 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d68255, d68550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68255, d68550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4095 q ha hb
  have h6 (q : Pattern) (ha : d68256 q = 1) (hb : d68551 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d68256, d68551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68256, d68551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d68257 q = 1) (hb : d68552 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d68257, d68552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68257, d68552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68258 q = 1) (hb : d68553 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d68258, d68553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68258, d68553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68259 q = 1) (hb : d68554 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d68259, d68554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d68259, d68554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d68291 q = 1) (hb : d68572 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d68291, d68572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68291, d68572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4100 q ha hb
  have h11 (q : Pattern) (ha : d68292 q = 1) (hb : d68573 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d68292, d68573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68292, d68573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d68293 q = 1) (hb : d68574 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d68293, d68574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68293, d68574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d68294 q = 1) (hb : d68575 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d68294, d68575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68294, d68575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d68295 q = 1) (hb : d68576 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d68295, d68576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68295, d68576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d68296 q = 1) (hb : d68577 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d68296, d68577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68296, d68577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro4102 (p : Pattern) (ha : d67696 p = 1) (hb : d68311 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d621 q = 1) (hb : d52328 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d621, d52328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79 q ha hb
    | true =>
      simp only [d621, d52328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65 q ha hb
  have h2 (q : Pattern) (ha : d4413 q = 1) (hb : d68302 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4413, d68302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4413, d68302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52331 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d67686 q = 1) (hb : d68303 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67686, d68303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67686, d68303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d67694 q = 1) (hb : d68304 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67694, d68304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67694, d68304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67695 q = 1) (hb : d68305 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67695, d68305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67695, d68305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67696 q = 1) (hb : d68311 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67696, d68311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67696, d68311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4103 (p : Pattern) (ha : d67705 p = 1) (hb : d68321 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d690 q = 1) (hb : d52394 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d690, d52394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro84 q ha hb
    | true =>
      simp only [d690, d52394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro85 q ha hb
  have h2 (q : Pattern) (ha : d4428 q = 1) (hb : d68317 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4428, d68317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4428, d68317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52402 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d67702 q = 1) (hb : d68318 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67702, d68318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67702, d68318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d67703 q = 1) (hb : d68319 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67703, d68319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67703, d68319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67704 q = 1) (hb : d68320 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67704, d68320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67704, d68320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67705 q = 1) (hb : d68321 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67705, d68321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67705, d68321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4104 (p : Pattern) (ha : d68301 p = 1) (hb : d68580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d561 q = 1) (hb : d52308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d561, d52308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91 q ha hb
    | true =>
      simp only [d561, d52308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62 q ha hb
  have h2 (q : Pattern) (ha : d4408 q = 1) (hb : d68297 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4408, d68297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4408, d68297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52311 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d67682 q = 1) (hb : d68298 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67682, d68298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67682, d68298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68299 q = 1) (hb : d68578 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68299, d68578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68299, d68578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d68300 q = 1) (hb : d68579 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68300, d68579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68300, d68579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d68301 q = 1) (hb : d68580 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68301, d68580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68301, d68580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4105 (p : Pattern) (ha : d68306 p = 1) (hb : d68581 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d561 q = 1) (hb : d52308 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d561, d52308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro91 q ha hb
    | true =>
      simp only [d561, d52308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro62 q ha hb
  have h2 (q : Pattern) (ha : d4408 q = 1) (hb : d68297 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4408, d68297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4408, d68297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52311 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d67682 q = 1) (hb : d68298 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67682, d68298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67682, d68298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68299 q = 1) (hb : d68578 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68299, d68578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68299, d68578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d68300 q = 1) (hb : d68579 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68300, d68579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68300, d68579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d621 q = 1) (hb : d52328 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d621, d52328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79 q ha hb
    | true =>
      simp only [d621, d52328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro65 q ha hb
  have h8 (q : Pattern) (ha : d4413 q = 1) (hb : d68302 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4413, d68302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4413, d68302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52331 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d67686 q = 1) (hb : d68303 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67686, d68303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d67686, d68303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d67694 q = 1) (hb : d68304 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67694, d68304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67694, d68304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d67695 q = 1) (hb : d68305 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67695, d68305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67695, d68305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d68306 q = 1) (hb : d68581 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68306, d68581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d68306, d68581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  exact h13 p ha hb
theorem andIntro4106 (p : Pattern) (ha : d68327 p = 1) (hb : d68594 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68307 q = 1) (hb : d68582 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68307, d68582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4104 q ha hb
    | true =>
      simp only [d68307, d68582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4105 q ha hb
  have h2 (q : Pattern) (ha : d68308 q = 1) (hb : d68583 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68308, d68583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68308, d68583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68309 q = 1) (hb : d68584 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68309, d68584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68309, d68584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68310 q = 1) (hb : d68585 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68310, d68585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68310, d68585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d67697 q = 1) (hb : d68312 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67697, d68312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67697, d68312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4102 q ha hb
  have h6 (q : Pattern) (ha : d68313 q = 1) (hb : d68586 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68313, d68586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d68313, d68586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d68314 q = 1) (hb : d68587 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68314, d68587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d68314, d68587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d68315 q = 1) (hb : d68588 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68315, d68588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d68315, d68588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d68316 q = 1) (hb : d68589 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68316, d68589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68316, d68589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d67706 q = 1) (hb : d68322 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67706, d68322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67706, d68322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4103 q ha hb
  have h11 (q : Pattern) (ha : d68323 q = 1) (hb : d68590 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68323, d68590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d68323, d68590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d68324 q = 1) (hb : d68591 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68324, d68591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d68324, d68591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d68325 q = 1) (hb : d68592 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68325, d68592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d68325, d68592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d68326 q = 1) (hb : d68593 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68326, d68593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d68326, d68593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d68327 q = 1) (hb : d68594 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d68327, d68594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68327, d68594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro4107 (p : Pattern) (ha : d68333 p = 1) (hb : d68600 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68328 q = 1) (hb : d68595 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d68328, d68595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68328, d68595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4106 q ha hb
  have h2 (q : Pattern) (ha : d68329 q = 1) (hb : d68596 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d68329, d68596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68329, d68596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68330 q = 1) (hb : d68597 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d68330, d68597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68330, d68597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d68331 q = 1) (hb : d68598 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d68331, d68598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68331, d68598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68332 q = 1) (hb : d68599 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d68332, d68599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68332, d68599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d68333 q = 1) (hb : d68600 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d68333, d68600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68333, d68600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4108 (p : Pattern) (ha : d67733 p = 1) (hb : d68349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d927 q = 1) (hb : d52549 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d927, d52549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro125 q ha hb
    | true =>
      simp only [d927, d52549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro109 q ha hb
  have h2 (q : Pattern) (ha : d4451 q = 1) (hb : d68340 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4451, d68340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4451, d68340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52552 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d67723 q = 1) (hb : d68341 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67723, d68341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67723, d68341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d67731 q = 1) (hb : d68342 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67731, d68342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67731, d68342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67732 q = 1) (hb : d68343 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67732, d68343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67732, d68343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67733 q = 1) (hb : d68349 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67733, d68349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67733, d68349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4109 (p : Pattern) (ha : d67742 p = 1) (hb : d68359 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1012 q = 1) (hb : d52631 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1012, d52631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro131 q ha hb
    | true =>
      simp only [d1012, d52631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro132 q ha hb
  have h2 (q : Pattern) (ha : d4466 q = 1) (hb : d68355 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4466, d68355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4466, d68355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52639 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d67739 q = 1) (hb : d68356 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67739, d68356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67739, d68356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d67740 q = 1) (hb : d68357 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67740, d68357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67740, d68357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67741 q = 1) (hb : d68358 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67741, d68358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67741, d68358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67742 q = 1) (hb : d68359 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67742, d68359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67742, d68359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4110 (p : Pattern) (ha : d68339 p = 1) (hb : d68604 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d852 q = 1) (hb : d52529 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d852, d52529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro138 q ha hb
    | true =>
      simp only [d852, d52529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106 q ha hb
  have h2 (q : Pattern) (ha : d4446 q = 1) (hb : d68335 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4446, d68335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4446, d68335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52532 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d67719 q = 1) (hb : d68336 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67719, d68336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67719, d68336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68337 q = 1) (hb : d68602 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68337, d68602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68337, d68602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d68338 q = 1) (hb : d68603 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68338, d68603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68338, d68603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d68339 q = 1) (hb : d68604 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68339, d68604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68339, d68604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4111 (p : Pattern) (ha : d68344 p = 1) (hb : d68605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d852 q = 1) (hb : d52529 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d852, d52529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro138 q ha hb
    | true =>
      simp only [d852, d52529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro106 q ha hb
  have h2 (q : Pattern) (ha : d4446 q = 1) (hb : d68335 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4446, d68335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4446, d68335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52532 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d67719 q = 1) (hb : d68336 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67719, d68336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67719, d68336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68337 q = 1) (hb : d68602 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68337, d68602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68337, d68602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d68338 q = 1) (hb : d68603 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68338, d68603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68338, d68603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d927 q = 1) (hb : d52549 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d927, d52549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro125 q ha hb
    | true =>
      simp only [d927, d52549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro109 q ha hb
  have h8 (q : Pattern) (ha : d4451 q = 1) (hb : d68340 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4451, d68340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4451, d68340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52552 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d67723 q = 1) (hb : d68341 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67723, d68341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d67723, d68341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d67731 q = 1) (hb : d68342 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67731, d68342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67731, d68342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d67732 q = 1) (hb : d68343 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67732, d68343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67732, d68343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d68344 q = 1) (hb : d68605 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68344, d68605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d68344, d68605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  exact h13 p ha hb
theorem andIntro4112 (p : Pattern) (ha : d68365 p = 1) (hb : d68618 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68345 q = 1) (hb : d68606 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68345, d68606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4110 q ha hb
    | true =>
      simp only [d68345, d68606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4111 q ha hb
  have h2 (q : Pattern) (ha : d68346 q = 1) (hb : d68607 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68346, d68607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68346, d68607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68347 q = 1) (hb : d68608 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68347, d68608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68347, d68608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68348 q = 1) (hb : d68609 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68348, d68609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68348, d68609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d67734 q = 1) (hb : d68350 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67734, d68350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67734, d68350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4108 q ha hb
  have h6 (q : Pattern) (ha : d68351 q = 1) (hb : d68610 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68351, d68610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d68351, d68610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d68352 q = 1) (hb : d68611 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68352, d68611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d68352, d68611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d68353 q = 1) (hb : d68612 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68353, d68612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d68353, d68612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d68354 q = 1) (hb : d68613 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68354, d68613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68354, d68613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d67743 q = 1) (hb : d68360 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67743, d68360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67743, d68360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4109 q ha hb
  have h11 (q : Pattern) (ha : d68361 q = 1) (hb : d68614 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68361, d68614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d68361, d68614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d68362 q = 1) (hb : d68615 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68362, d68615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d68362, d68615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d68363 q = 1) (hb : d68616 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68363, d68616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d68363, d68616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d68364 q = 1) (hb : d68617 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68364, d68617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d68364, d68617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d68365 q = 1) (hb : d68618 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d68365, d68618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68365, d68618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro4113 (p : Pattern) (ha : d68371 p = 1) (hb : d68624 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68366 q = 1) (hb : d68619 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d68366, d68619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68366, d68619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4112 q ha hb
  have h2 (q : Pattern) (ha : d68367 q = 1) (hb : d68620 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d68367, d68620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68367, d68620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68368 q = 1) (hb : d68621 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d68368, d68621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68368, d68621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d68369 q = 1) (hb : d68622 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d68369, d68622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68369, d68622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68370 q = 1) (hb : d68623 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d68370, d68623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68370, d68623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d68371 q = 1) (hb : d68624 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d68371, d68624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68371, d68624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4114 (p : Pattern) (ha : d67771 p = 1) (hb : d68388 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1338 q = 1) (hb : d52829 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1338, d52829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro177 q ha hb
    | true =>
      simp only [d1338, d52829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro161 q ha hb
  have h2 (q : Pattern) (ha : d4490 q = 1) (hb : d68379 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4490, d68379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4490, d68379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52832 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d67761 q = 1) (hb : d68380 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67761, d68380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67761, d68380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d67769 q = 1) (hb : d68381 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67769, d68381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67769, d68381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67770 q = 1) (hb : d68382 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67770, d68382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67770, d68382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67771 q = 1) (hb : d68388 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67771, d68388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67771, d68388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4115 (p : Pattern) (ha : d67780 p = 1) (hb : d68398 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1437 q = 1) (hb : d52925 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1437, d52925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro183 q ha hb
    | true =>
      simp only [d1437, d52925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro184 q ha hb
  have h2 (q : Pattern) (ha : d4505 q = 1) (hb : d68394 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4505, d68394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4505, d68394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52933 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d67777 q = 1) (hb : d68395 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67777, d68395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67777, d68395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d67778 q = 1) (hb : d68396 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67778, d68396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67778, d68396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67779 q = 1) (hb : d68397 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67779, d68397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67779, d68397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67780 q = 1) (hb : d68398 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67780, d68398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67780, d68398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4116 (p : Pattern) (ha : d68378 p = 1) (hb : d68629 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1228 q = 1) (hb : d52809 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1228, d52809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro190 q ha hb
    | true =>
      simp only [d1228, d52809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro158 q ha hb
  have h2 (q : Pattern) (ha : d4485 q = 1) (hb : d68374 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4485, d68374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4485, d68374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52812 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d67757 q = 1) (hb : d68375 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67757, d68375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67757, d68375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68376 q = 1) (hb : d68627 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68376, d68627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68376, d68627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d68377 q = 1) (hb : d68628 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68377, d68628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68377, d68628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d68378 q = 1) (hb : d68629 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68378, d68629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68378, d68629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4117 (p : Pattern) (ha : d68383 p = 1) (hb : d68630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1228 q = 1) (hb : d52809 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1228, d52809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro190 q ha hb
    | true =>
      simp only [d1228, d52809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro158 q ha hb
  have h2 (q : Pattern) (ha : d4485 q = 1) (hb : d68374 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4485, d68374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4485, d68374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d52812 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d67757 q = 1) (hb : d68375 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67757, d68375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67757, d68375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68376 q = 1) (hb : d68627 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68376, d68627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68376, d68627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d68377 q = 1) (hb : d68628 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68377, d68628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68377, d68628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1338 q = 1) (hb : d52829 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1338, d52829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro177 q ha hb
    | true =>
      simp only [d1338, d52829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro161 q ha hb
  have h8 (q : Pattern) (ha : d4490 q = 1) (hb : d68379 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4490, d68379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4490, d68379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52832 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d67761 q = 1) (hb : d68380 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67761, d68380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d67761, d68380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d67769 q = 1) (hb : d68381 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67769, d68381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67769, d68381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d67770 q = 1) (hb : d68382 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67770, d68382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67770, d68382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d68383 q = 1) (hb : d68630 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68383, d68630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d68383, d68630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  exact h13 p ha hb
theorem andIntro4118 (p : Pattern) (ha : d68404 p = 1) (hb : d68643 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68384 q = 1) (hb : d68631 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68384, d68631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4116 q ha hb
    | true =>
      simp only [d68384, d68631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4117 q ha hb
  have h2 (q : Pattern) (ha : d68385 q = 1) (hb : d68632 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68385, d68632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68385, d68632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68386 q = 1) (hb : d68633 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68386, d68633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68386, d68633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68387 q = 1) (hb : d68634 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68387, d68634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68387, d68634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d67772 q = 1) (hb : d68389 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67772, d68389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67772, d68389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4114 q ha hb
  have h6 (q : Pattern) (ha : d68390 q = 1) (hb : d68635 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68390, d68635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d68390, d68635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d68391 q = 1) (hb : d68636 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68391, d68636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d68391, d68636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d68392 q = 1) (hb : d68637 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68392, d68637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d68392, d68637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d68393 q = 1) (hb : d68638 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68393, d68638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68393, d68638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d67781 q = 1) (hb : d68399 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67781, d68399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67781, d68399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4115 q ha hb
  have h11 (q : Pattern) (ha : d68400 q = 1) (hb : d68639 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68400, d68639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d68400, d68639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d68401 q = 1) (hb : d68640 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68401, d68640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d68401, d68640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d68402 q = 1) (hb : d68641 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68402, d68641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d68402, d68641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d68403 q = 1) (hb : d68642 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68403, d68642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d68403, d68642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d68404 q = 1) (hb : d68643 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d68404, d68643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68404, d68643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro4119 (p : Pattern) (ha : d68410 p = 1) (hb : d68649 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68405 q = 1) (hb : d68644 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d68405, d68644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68405, d68644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4118 q ha hb
  have h2 (q : Pattern) (ha : d68406 q = 1) (hb : d68645 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d68406, d68645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68406, d68645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68407 q = 1) (hb : d68646 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d68407, d68646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68407, d68646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d68408 q = 1) (hb : d68647 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d68408, d68647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68408, d68647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68409 q = 1) (hb : d68648 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d68409, d68648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68409, d68648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d68410 q = 1) (hb : d68649 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d68410, d68649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68410, d68649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4120 (p : Pattern) (ha : d67810 p = 1) (hb : d68428 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1815 q = 1) (hb : d53144 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1815, d53144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro233 q ha hb
    | true =>
      simp only [d1815, d53144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro219 q ha hb
  have h2 (q : Pattern) (ha : d4530 q = 1) (hb : d68419 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4530, d68419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4530, d68419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53147 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d67800 q = 1) (hb : d68420 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67800, d68420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67800, d68420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d67808 q = 1) (hb : d68421 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67808, d68421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67808, d68421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67809 q = 1) (hb : d68422 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67809, d68422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67809, d68422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67810 q = 1) (hb : d68428 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67810, d68428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67810, d68428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4121 (p : Pattern) (ha : d67819 p = 1) (hb : d68438 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1914 q = 1) (hb : d53240 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1914, d53240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro239 q ha hb
    | true =>
      simp only [d1914, d53240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro240 q ha hb
  have h2 (q : Pattern) (ha : d4545 q = 1) (hb : d68434 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4545, d68434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4545, d68434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53248 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d67816 q = 1) (hb : d68435 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67816, d68435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67816, d68435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d67817 q = 1) (hb : d68436 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67817, d68436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67817, d68436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67818 q = 1) (hb : d68437 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67818, d68437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67818, d68437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67819 q = 1) (hb : d68438 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67819, d68438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67819, d68438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4122 (p : Pattern) (ha : d68418 p = 1) (hb : d68655 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1683 q = 1) (hb : d53124 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1683, d53124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro246 q ha hb
    | true =>
      simp only [d1683, d53124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro216 q ha hb
  have h2 (q : Pattern) (ha : d4525 q = 1) (hb : d68414 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4525, d68414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4525, d68414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53127 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d67796 q = 1) (hb : d68415 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67796, d68415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67796, d68415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68416 q = 1) (hb : d68653 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68416, d68653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68416, d68653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d68417 q = 1) (hb : d68654 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68417, d68654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68417, d68654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d68418 q = 1) (hb : d68655 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68418, d68655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68418, d68655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4123 (p : Pattern) (ha : d68423 p = 1) (hb : d68656 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1683 q = 1) (hb : d53124 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1683, d53124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro246 q ha hb
    | true =>
      simp only [d1683, d53124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro216 q ha hb
  have h2 (q : Pattern) (ha : d4525 q = 1) (hb : d68414 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4525, d68414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4525, d68414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53127 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d67796 q = 1) (hb : d68415 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67796, d68415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67796, d68415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68416 q = 1) (hb : d68653 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68416, d68653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68416, d68653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d68417 q = 1) (hb : d68654 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68417, d68654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68417, d68654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1815 q = 1) (hb : d53144 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1815, d53144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro233 q ha hb
    | true =>
      simp only [d1815, d53144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro219 q ha hb
  have h8 (q : Pattern) (ha : d4530 q = 1) (hb : d68419 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4530, d68419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4530, d68419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53147 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d67800 q = 1) (hb : d68420 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67800, d68420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d67800, d68420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d67808 q = 1) (hb : d68421 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67808, d68421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67808, d68421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d67809 q = 1) (hb : d68422 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67809, d68422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67809, d68422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d68423 q = 1) (hb : d68656 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68423, d68656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d68423, d68656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  exact h13 p ha hb
theorem andIntro4124 (p : Pattern) (ha : d68444 p = 1) (hb : d68669 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68424 q = 1) (hb : d68657 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68424, d68657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4122 q ha hb
    | true =>
      simp only [d68424, d68657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4123 q ha hb
  have h2 (q : Pattern) (ha : d68425 q = 1) (hb : d68658 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68425, d68658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68425, d68658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68426 q = 1) (hb : d68659 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68426, d68659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68426, d68659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68427 q = 1) (hb : d68660 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68427, d68660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68427, d68660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d67811 q = 1) (hb : d68429 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67811, d68429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67811, d68429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4120 q ha hb
  have h6 (q : Pattern) (ha : d68430 q = 1) (hb : d68661 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68430, d68661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d68430, d68661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d68431 q = 1) (hb : d68662 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68431, d68662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d68431, d68662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d68432 q = 1) (hb : d68663 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68432, d68663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d68432, d68663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d68433 q = 1) (hb : d68664 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68433, d68664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68433, d68664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d67820 q = 1) (hb : d68439 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67820, d68439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67820, d68439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4121 q ha hb
  have h11 (q : Pattern) (ha : d68440 q = 1) (hb : d68665 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68440, d68665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d68440, d68665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d68441 q = 1) (hb : d68666 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68441, d68666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d68441, d68666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d68442 q = 1) (hb : d68667 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68442, d68667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d68442, d68667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d68443 q = 1) (hb : d68668 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68443, d68668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d68443, d68668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d68444 q = 1) (hb : d68669 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d68444, d68669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68444, d68669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro4125 (p : Pattern) (ha : d68450 p = 1) (hb : d68675 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68445 q = 1) (hb : d68670 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d68445, d68670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68445, d68670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4124 q ha hb
  have h2 (q : Pattern) (ha : d68446 q = 1) (hb : d68671 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d68446, d68671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68446, d68671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68447 q = 1) (hb : d68672 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d68447, d68672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68447, d68672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d68448 q = 1) (hb : d68673 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d68448, d68673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68448, d68673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68449 q = 1) (hb : d68674 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d68449, d68674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68449, d68674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d68450 q = 1) (hb : d68675 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d68450, d68675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68450, d68675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4126 (p : Pattern) (ha : d67850 p = 1) (hb : d68469 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2293 q = 1) (hb : d53461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2293, d53461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro292 q ha hb
    | true =>
      simp only [d2293, d53461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro278 q ha hb
  have h2 (q : Pattern) (ha : d4571 q = 1) (hb : d68460 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4571, d68460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4571, d68460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53464 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d67840 q = 1) (hb : d68461 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67840, d68461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67840, d68461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d67848 q = 1) (hb : d68462 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67848, d68462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67848, d68462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67849 q = 1) (hb : d68463 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67849, d68463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67849, d68463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67850 q = 1) (hb : d68469 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67850, d68469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67850, d68469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4127 (p : Pattern) (ha : d67859 p = 1) (hb : d68479 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2392 q = 1) (hb : d53557 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2392, d53557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro298 q ha hb
    | true =>
      simp only [d2392, d53557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro299 q ha hb
  have h2 (q : Pattern) (ha : d4586 q = 1) (hb : d68475 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4586, d68475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4586, d68475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53565 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d67856 q = 1) (hb : d68476 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67856, d68476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67856, d68476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d67857 q = 1) (hb : d68477 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67857, d68477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67857, d68477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d67858 q = 1) (hb : d68478 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67858, d68478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67858, d68478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d67859 q = 1) (hb : d68479 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d67859, d68479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67859, d68479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4128 (p : Pattern) (ha : d68459 p = 1) (hb : d68682 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2162 q = 1) (hb : d53441 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2162, d53441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro305 q ha hb
    | true =>
      simp only [d2162, d53441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro275 q ha hb
  have h2 (q : Pattern) (ha : d4566 q = 1) (hb : d68455 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4566, d68455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4566, d68455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53444 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d67836 q = 1) (hb : d68456 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67836, d68456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67836, d68456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68457 q = 1) (hb : d68680 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68457, d68680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68457, d68680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d68458 q = 1) (hb : d68681 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68458, d68681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68458, d68681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d68459 q = 1) (hb : d68682 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68459, d68682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68459, d68682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4129 (p : Pattern) (ha : d68464 p = 1) (hb : d68683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2162 q = 1) (hb : d53441 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2162, d53441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro305 q ha hb
    | true =>
      simp only [d2162, d53441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro275 q ha hb
  have h2 (q : Pattern) (ha : d4566 q = 1) (hb : d68455 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4566, d68455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4566, d68455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53444 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d67836 q = 1) (hb : d68456 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67836, d68456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d67836, d68456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68457 q = 1) (hb : d68680 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d68457, d68680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68457, d68680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d68458 q = 1) (hb : d68681 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d68458, d68681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68458, d68681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2293 q = 1) (hb : d53461 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2293, d53461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro292 q ha hb
    | true =>
      simp only [d2293, d53461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro278 q ha hb
  have h8 (q : Pattern) (ha : d4571 q = 1) (hb : d68460 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4571, d68460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4571, d68460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53464 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d67840 q = 1) (hb : d68461 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d67840, d68461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d67840, d68461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d67848 q = 1) (hb : d68462 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d67848, d68462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67848, d68462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d67849 q = 1) (hb : d68463 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d67849, d68463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67849, d68463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d68464 q = 1) (hb : d68683 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d68464, d68683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d68464, d68683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  exact h13 p ha hb
theorem andIntro4130 (p : Pattern) (ha : d68485 p = 1) (hb : d68696 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68465 q = 1) (hb : d68684 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d68465, d68684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4128 q ha hb
    | true =>
      simp only [d68465, d68684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4129 q ha hb
  have h2 (q : Pattern) (ha : d68466 q = 1) (hb : d68685 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68466, d68685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68466, d68685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68467 q = 1) (hb : d68686 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68467, d68686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68467, d68686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68468 q = 1) (hb : d68687 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68468, d68687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68468, d68687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d67851 q = 1) (hb : d68470 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67851, d68470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67851, d68470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4126 q ha hb
  have h6 (q : Pattern) (ha : d68471 q = 1) (hb : d68688 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68471, d68688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d68471, d68688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d68472 q = 1) (hb : d68689 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68472, d68689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d68472, d68689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d68473 q = 1) (hb : d68690 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68473, d68690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d68473, d68690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d68474 q = 1) (hb : d68691 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68474, d68691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68474, d68691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d67860 q = 1) (hb : d68480 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d67860, d68480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d67860, d68480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4127 q ha hb
  have h11 (q : Pattern) (ha : d68481 q = 1) (hb : d68692 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d68481, d68692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d68481, d68692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d68482 q = 1) (hb : d68693 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d68482, d68693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d68482, d68693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d68483 q = 1) (hb : d68694 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d68483, d68694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d68483, d68694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d68484 q = 1) (hb : d68695 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d68484, d68695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d68484, d68695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d68485 q = 1) (hb : d68696 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d68485, d68696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d68485, d68696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro4131 (p : Pattern) (ha : d68491 p = 1) (hb : d68702 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68486 q = 1) (hb : d68697 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d68486, d68697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68486, d68697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4130 q ha hb
  have h2 (q : Pattern) (ha : d68487 q = 1) (hb : d68698 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d68487, d68698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68487, d68698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d68488 q = 1) (hb : d68699 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d68488, d68699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68488, d68699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d68489 q = 1) (hb : d68700 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d68489, d68700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68489, d68700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68490 q = 1) (hb : d68701 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d68490, d68701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68490, d68701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d68491 q = 1) (hb : d68702 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d68491, d68702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68491, d68702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4132 (p : Pattern) (ha : d68497 p = 1) (hb : d68708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d68334 q = 1) (hb : d68601 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d68334, d68601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4101 q ha hb
    | true =>
      simp only [d68334, d68601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4107 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d68372 q = 1) (hb : d68625 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d68372, d68625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68372, d68625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4113 q ha hb
  have h3 (q : Pattern) (ha : d68373 q = 1) (hb : d68626 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d68373, d68626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d68373, d68626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d68411 q = 1) (hb : d68650 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d68411, d68650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68411, d68650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4119 q ha hb
  have h5 (q : Pattern) (ha : d68412 q = 1) (hb : d68651 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d68412, d68651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68412, d68651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d68413 q = 1) (hb : d68652 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d68413, d68652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68413, d68652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d68451 q = 1) (hb : d68676 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d68451, d68676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68451, d68676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4125 q ha hb
  have h8 (q : Pattern) (ha : d68452 q = 1) (hb : d68677 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d68452, d68677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68452, d68677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d68453 q = 1) (hb : d68678 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d68453, d68678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68453, d68678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d68454 q = 1) (hb : d68679 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d68454, d68679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d68454, d68679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d68492 q = 1) (hb : d68703 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d68492, d68703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68492, d68703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4131 q ha hb
  have h12 (q : Pattern) (ha : d68493 q = 1) (hb : d68704 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d68493, d68704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68493, d68704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d68494 q = 1) (hb : d68705 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d68494, d68705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68494, d68705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d68495 q = 1) (hb : d68706 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d68495, d68706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d68495, d68706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d68496 q = 1) (hb : d68707 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d68496, d68707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d68496, d68707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d68497 q = 1) (hb : d68708 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d68497, d68708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d68497, d68708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro4133 (p : Pattern) (ha : d68503 p = 1) (hb : d68714 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68498 q = 1) (hb : d68709 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d68498, d68709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4132 q ha hb
    | true =>
      simp only [d68498, d68709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d68499 q = 1) (hb : d68710 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d68499, d68710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68499, d68710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68500 q = 1) (hb : d68711 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d68500, d68711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68500, d68711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68501 q = 1) (hb : d68712 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d68501, d68712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68501, d68712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d68502 q = 1) (hb : d68713 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d68502, d68713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68502, d68713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d68503 q = 1) (hb : d68714 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d68503, d68714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68503, d68714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4134 (p : Pattern) (ha : d68509 p = 1) (hb : d68720 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68504 q = 1) (hb : d68715 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d68504, d68715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4133 q ha hb
    | true =>
      simp only [d68504, d68715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d68505 q = 1) (hb : d68716 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d68505, d68716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68505, d68716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68506 q = 1) (hb : d68717 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d68506, d68717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68506, d68717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68507 q = 1) (hb : d68718 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d68507, d68718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68507, d68718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d68508 q = 1) (hb : d68719 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d68508, d68719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68508, d68719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d68509 q = 1) (hb : d68720 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d68509, d68720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68509, d68720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4135 (p : Pattern) (ha : d68515 p = 1) (hb : d68726 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68510 q = 1) (hb : d68721 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d68510, d68721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4134 q ha hb
    | true =>
      simp only [d68510, d68721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d68511 q = 1) (hb : d68722 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d68511, d68722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68511, d68722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68512 q = 1) (hb : d68723 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d68512, d68723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68512, d68723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68513 q = 1) (hb : d68724 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d68513, d68724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68513, d68724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d68514 q = 1) (hb : d68725 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d68514, d68725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68514, d68725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d68515 q = 1) (hb : d68726 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d68515, d68726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68515, d68726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4136 (p : Pattern) (ha : d68521 p = 1) (hb : d68732 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68516 q = 1) (hb : d68727 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d68516, d68727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4135 q ha hb
    | true =>
      simp only [d68516, d68727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d68517 q = 1) (hb : d68728 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d68517, d68728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68517, d68728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68518 q = 1) (hb : d68729 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d68518, d68729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68518, d68729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68519 q = 1) (hb : d68730 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d68519, d68730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68519, d68730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d68520 q = 1) (hb : d68731 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d68520, d68731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68520, d68731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d68521 q = 1) (hb : d68732 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d68521, d68732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68521, d68732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4137 (p : Pattern) (ha : d68527 p = 1) (hb : d68738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68522 q = 1) (hb : d68733 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d68522, d68733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4136 q ha hb
    | true =>
      simp only [d68522, d68733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d68523 q = 1) (hb : d68734 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d68523, d68734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68523, d68734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68524 q = 1) (hb : d68735 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d68524, d68735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68524, d68735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68525 q = 1) (hb : d68736 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d68525, d68736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68525, d68736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d68526 q = 1) (hb : d68737 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d68526, d68737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68526, d68737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d68527 q = 1) (hb : d68738 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d68527, d68738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68527, d68738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4138 (p : Pattern) (ha : d68533 p = 1) (hb : d68744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68528 q = 1) (hb : d68739 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d68528, d68739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4137 q ha hb
    | true =>
      simp only [d68528, d68739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d68529 q = 1) (hb : d68740 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d68529, d68740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68529, d68740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68530 q = 1) (hb : d68741 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d68530, d68741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68530, d68741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68531 q = 1) (hb : d68742 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d68531, d68742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68531, d68742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d68532 q = 1) (hb : d68743 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d68532, d68743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68532, d68743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d68533 q = 1) (hb : d68744 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d68533, d68744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68533, d68744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4139 (p : Pattern) (ha : d68539 p = 1) (hb : d68750 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d68534 q = 1) (hb : d68745 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d68534, d68745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4138 q ha hb
    | true =>
      simp only [d68534, d68745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d68535 q = 1) (hb : d68746 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d68535, d68746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d68535, d68746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d68536 q = 1) (hb : d68747 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d68536, d68747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d68536, d68747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d68537 q = 1) (hb : d68748 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d68537, d68748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d68537, d68748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d68538 q = 1) (hb : d68749 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d68538, d68749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68538, d68749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d68539 q = 1) (hb : d68750 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d68539, d68750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d68539, d68750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4140 (p : Pattern) (ha : d53647 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4004 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4005 q ha hb
  have h2 (q : Pattern) (ha : d113 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53637 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53638 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d407 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4015 q ha hb
  have h6 (q : Pattern) (ha : d53639 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53640 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53641 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53642 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d463 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4016 q ha hb
  have h11 (q : Pattern) (ha : d53643 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53644 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53645 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53646 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53647 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro4141 (p : Pattern) (ha : d53655 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d204 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d287 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d287, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d288 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d288, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d289 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d290 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53655 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4142 (p : Pattern) (ha : d53665 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d244 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53661 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53661, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53661, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53662 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53662, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53662, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53663 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53664 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53665 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4143 (p : Pattern) (ha : d53671 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d292 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4012 q ha hb
    | true =>
      simp only [d292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4013 q ha hb
  have h2 (q : Pattern) (ha : d293 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53653 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53654 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53656 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4141 q ha hb
  have h6 (q : Pattern) (ha : d53657 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53658 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53659 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53660 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53666 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4142 q ha hb
  have h11 (q : Pattern) (ha : d53667 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53668 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53669 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53670 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53671 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro4144 (p : Pattern) (ha : d53677 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4140 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53672 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4143 q ha hb
  have h7 (q : Pattern) (ha : d53673 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53674 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53675 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53676 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53677 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro4145 (p : Pattern) (ha : d53680 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d502 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d503 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d503, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d503, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d504 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d504, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d504, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d505 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d506 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53680 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4146 (p : Pattern) (ha : d53691 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53686 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53687 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53687, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53687, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53688 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53688, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53688, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53689 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53690 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53691 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4147 (p : Pattern) (ha : d53697 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d508 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4023 q ha hb
    | true =>
      simp only [d508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4024 q ha hb
  have h2 (q : Pattern) (ha : d509 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53678 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53679 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53681 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4145 q ha hb
  have h6 (q : Pattern) (ha : d53682 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53683 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53684 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53685 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53692 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4146 q ha hb
  have h11 (q : Pattern) (ha : d53693 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53694 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53695 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53696 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53697 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro4148 (p : Pattern) (ha : d53703 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53698 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4147 q ha hb
  have h2 (q : Pattern) (ha : d53699 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53700 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53701 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53702 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53703 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4149 (p : Pattern) (ha : d53707 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d794 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d795 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d795, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d795, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d796 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d796, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d796, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d797 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d798 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53707 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4150 (p : Pattern) (ha : d53718 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53713 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53714 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53714, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53714, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53715 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53715, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53715, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53716 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53717 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53718 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4151 (p : Pattern) (ha : d53724 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d800 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4035 q ha hb
    | true =>
      simp only [d800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4036 q ha hb
  have h2 (q : Pattern) (ha : d801 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53705 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53706 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53708 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4149 q ha hb
  have h6 (q : Pattern) (ha : d53709 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53710 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53711 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53712 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53719 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4150 q ha hb
  have h11 (q : Pattern) (ha : d53720 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53721 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53722 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53723 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53724 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro4152 (p : Pattern) (ha : d53730 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53725 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4151 q ha hb
  have h2 (q : Pattern) (ha : d53726 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53727 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53728 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53729 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53730 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4153 (p : Pattern) (ha : d53735 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1173 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1174 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1174, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1174, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1175 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1175, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1175, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1176 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1177 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53735 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4154 (p : Pattern) (ha : d53746 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53741 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53742 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53742, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53742, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53743 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53743, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53743, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53744 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53745 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53746 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4155 (p : Pattern) (ha : d53752 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1179 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4047 q ha hb
    | true =>
      simp only [d1179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4048 q ha hb
  have h2 (q : Pattern) (ha : d1180 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53733 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53734 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53736 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4153 q ha hb
  have h6 (q : Pattern) (ha : d53737 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53738 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53739 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53740 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53747 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4154 q ha hb
  have h11 (q : Pattern) (ha : d53748 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53749 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53750 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53751 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53752 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro4156 (p : Pattern) (ha : d53758 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53753 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4155 q ha hb
  have h2 (q : Pattern) (ha : d53754 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53755 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53756 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53757 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53758 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4157 (p : Pattern) (ha : d53764 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1634 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1635 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1635, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1635, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1636 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1636, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1636, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1637 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1638 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53764 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4158 (p : Pattern) (ha : d53775 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53770 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53771 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53771, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53771, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53772 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53772, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53772, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53773 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53774 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53775 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4159 (p : Pattern) (ha : d53781 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1640 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4059 q ha hb
    | true =>
      simp only [d1640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4060 q ha hb
  have h2 (q : Pattern) (ha : d1641 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53762 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53763 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53765 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4157 q ha hb
  have h6 (q : Pattern) (ha : d53766 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53767 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53768 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53769 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53776 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4158 q ha hb
  have h11 (q : Pattern) (ha : d53777 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53778 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53779 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53780 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53781 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro4160 (p : Pattern) (ha : d53787 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53782 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4159 q ha hb
  have h2 (q : Pattern) (ha : d53783 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53784 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53785 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53786 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53787 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4161 (p : Pattern) (ha : d53794 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2117 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2118 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2118, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2118, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d2119 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2119, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2119, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2120 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2121 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53794 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4162 (p : Pattern) (ha : d53805 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d53800 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d53801 q = 1) (hb : d68221 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d53801, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53801, d68221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d53802 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d53802, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53802, d68222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53803 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d53803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53804 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d53804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d53805 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d53805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4163 (p : Pattern) (ha : d53811 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2123 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4071 q ha hb
    | true =>
      simp only [d2123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4072 q ha hb
  have h2 (q : Pattern) (ha : d2124 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53792 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53793 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53795 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4161 q ha hb
  have h6 (q : Pattern) (ha : d53796 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53797 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53798 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53799 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53806 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d53806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4162 q ha hb
  have h11 (q : Pattern) (ha : d53807 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53808 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53809 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53810 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53811 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d53811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro4164 (p : Pattern) (ha : d53817 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53812 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4163 q ha hb
  have h2 (q : Pattern) (ha : d53813 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53814 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53815 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53816 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53817 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4165 (p : Pattern) (ha : d53823 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d53704 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4144 q ha hb
    | true =>
      simp only [d53704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4148 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53731 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4152 q ha hb
  have h3 (q : Pattern) (ha : d53732 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53759 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4156 q ha hb
  have h5 (q : Pattern) (ha : d53760 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53761 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53788 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4160 q ha hb
  have h8 (q : Pattern) (ha : d53789 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53790 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53791 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53818 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4164 q ha hb
  have h12 (q : Pattern) (ha : d53819 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53820 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d53821 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d53822 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d53822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d53823 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d53823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro4166 (p : Pattern) (ha : d53829 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53824 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d53824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4165 q ha hb
    | true =>
      simp only [d53824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53825 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d53825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53826 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d53826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53827 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d53827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53828 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d53828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53829 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d53829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4167 (p : Pattern) (ha : d53835 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53830 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d53830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4166 q ha hb
    | true =>
      simp only [d53830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53831 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d53831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53832 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d53832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53833 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d53833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53834 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d53834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53835 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d53835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4168 (p : Pattern) (ha : d53841 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53836 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d53836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4167 q ha hb
    | true =>
      simp only [d53836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53837 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d53837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53838 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d53838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53839 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d53839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53840 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d53840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53841 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d53841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4169 (p : Pattern) (ha : d53847 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53842 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d53842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4168 q ha hb
    | true =>
      simp only [d53842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53843 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d53843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53844 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d53844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53845 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d53845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53846 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d53846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53847 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d53847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4170 (p : Pattern) (ha : d53853 p = 1) (hb : d68222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53848 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d53848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4169 q ha hb
    | true =>
      simp only [d53848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53849 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d53849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53850 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d53850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53851 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d53851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53852 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d53852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53853 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d53853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4171 (p : Pattern) (ha : d53859 p = 1) (hb : d68223 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53854 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d53854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4170 q ha hb
    | true =>
      simp only [d53854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53855 q = 1) (hb : d68222 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d53855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53856 q = 1) (hb : d68223 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d53856, d68223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53856, d68223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d68223 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d53857 q = 1) (hb : d68223 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d53857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53858 q = 1) (hb : d68223 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d53858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h8 (q : Pattern) (ha : d53859 q = 1) (hb : d68223 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d53859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h8 p ha hb
theorem andIntro4172 (p : Pattern) (ha : d53865 p = 1) (hb : d68223 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68223 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53860 q = 1) (hb : d68223 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d53860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4171 q ha hb
    | true =>
      simp only [d53860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d53861 q = 1) (hb : d68223 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d53861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53862 q = 1) (hb : d68223 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d53862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53863 q = 1) (hb : d68223 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d53863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d53864 q = 1) (hb : d68223 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d53864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d53865 q = 1) (hb : d68223 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d53865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro4173 (p : Pattern) (ha : d0 p = 1) (hb : d68539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68539 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro4174 (p : Pattern) (ha : d0 p = 1) (hb : d4650 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d4650 q = 1) : d0 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro4175 (p : Pattern) (ha : d58432 p = 1) (hb : d58743 p = 1) : d58743 p = 1 := by
  have h0 (q : Pattern) (ha : d58432 q = 1) (hb : d58743 q = 1) : d58743 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro4176 (p : Pattern) (ha : d52073 p = 1) (hb : d58614 p = 1) : d0 p = 1 := by
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
  have h6 (q : Pattern) (ha : d51647 q = 1) (hb : d52030 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51647, d52030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro31 q ha hb
    | true =>
      simp only [d51647, d52030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro34 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52032 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d52033 q = 1) (hb : d58610 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52033, d58610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d52033, d58610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d52034 q = 1) (hb : d58611 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52034, d58611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d52034, d58611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d52035 q = 1) (hb : d58612 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52035, d58612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52035, d58612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4350 q = 1) (hb : d52039 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4350, d52039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4350, d52039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23 q ha hb
  have h12 (q : Pattern) (ha : d4351 q = 1) (hb : d52040 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4351, d52040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4351, d52040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d4352 q = 1) (hb : d52041 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4352, d52041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4352, d52041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d4353 q = 1) (hb : d52042 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4353, d52042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4353, d52042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d52043 q = 1) (hb : d58613 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52043, d58613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52043, d58613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d4360 q = 1) (hb : d52068 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4360, d52068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4360, d52068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro27 q ha hb
  have h17 (q : Pattern) (ha : d4361 q = 1) (hb : d52069 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4361, d52069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d4361, d52069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d4362 q = 1) (hb : d52070 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4362, d52070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d4362, d52070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d4363 q = 1) (hb : d52071 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4363, d52071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d4363, d52071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d4364 q = 1) (hb : d52072 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4364, d52072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4364, d52072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d52073 q = 1) (hb : d58614 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d52073, d58614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d52073, d58614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
  exact h21 p ha hb
theorem andIntro4177 (p : Pattern) (ha : d52215 p = 1) (hb : d58624 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285 q = 1) (hb : d52084 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, d52084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, d52084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36 q ha hb
  have h2 (q : Pattern) (ha : d286 q = 1) (hb : d52085 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, d52085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286, d52085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d292 q = 1) (hb : d52091 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d52091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36 q ha hb
    | true =>
      simp only [d292, d52091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37 q ha hb
  have h4 (q : Pattern) (ha : d293 q = 1) (hb : d52092 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d52092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293, d52092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d294 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, d52093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d294, d52093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51664 q = 1) (hb : d52162 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51664, d52162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro54 q ha hb
    | true =>
      simp only [d51664, d52162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro57 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52164 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d52165 q = 1) (hb : d58620 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52165, d58620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d52165, d58620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d52166 q = 1) (hb : d58621 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52166, d58621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d52166, d58621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d52167 q = 1) (hb : d58622 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52167, d58622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52167, d58622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4386 q = 1) (hb : d52171 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4386, d52171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4386, d52171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4387 q = 1) (hb : d52174 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4387, d52174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4387, d52174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d4388 q = 1) (hb : d52175 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4388, d52175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4388, d52175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4389 q = 1) (hb : d52176 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4389, d52176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4389, d52176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d52177 q = 1) (hb : d58623 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52177, d58623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52177, d58623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d4396 q = 1) (hb : d52204 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4396, d52204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4396, d52204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro50 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d4397 q = 1) (hb : d52211 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4397, d52211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d4397, d52211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d4398 q = 1) (hb : d52212 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4398, d52212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4398, d52212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d4399 q = 1) (hb : d52213 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4399, d52213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d4399, d52213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d4400 q = 1) (hb : d52214 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4400, d52214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d4400, d52214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d52215 q = 1) (hb : d58624 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d52215, d58624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d52215, d58624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
  exact h23 p ha hb
theorem andIntro4178 (p : Pattern) (ha : d52221 p = 1) (hb : d58630 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d52074 q = 1) (hb : d58615 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d52074, d58615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52074, d58615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4176 q ha hb
  have h6 (q : Pattern) (ha : d52075 q = 1) (hb : d58616 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d52075, d58616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52075, d58616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d52076 q = 1) (hb : d58617 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d52076, d58617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52076, d58617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d52077 q = 1) (hb : d58618 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d52077, d58618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52077, d58618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d52078 q = 1) (hb : d58619 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d52078, d58619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d52078, d58619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d52216 q = 1) (hb : d58625 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d52216, d58625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52216, d58625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4177 q ha hb
  have h11 (q : Pattern) (ha : d52217 q = 1) (hb : d58626 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d52217, d58626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52217, d58626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d52218 q = 1) (hb : d58627 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d52218, d58627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52218, d58627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d52219 q = 1) (hb : d58628 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d52219, d58628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52219, d58628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d52220 q = 1) (hb : d58629 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d52220, d58629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52220, d58629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d52221 q = 1) (hb : d58630 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d52221, d58630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d52221, d58630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro4179 (p : Pattern) (ha : d52419 p = 1) (hb : d58635 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d498 q = 1) (hb : d52245 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d498, d52245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d498, d52245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64 q ha hb
  have h2 (q : Pattern) (ha : d499 q = 1) (hb : d52246 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d499, d52246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d499, d52246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d508 q = 1) (hb : d52255 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d52255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro64 q ha hb
    | true =>
      simp only [d508, d52255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro67 q ha hb
  have h4 (q : Pattern) (ha : d509 q = 1) (hb : d52256 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d52256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d509, d52256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d510 q = 1) (hb : d52257 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d510, d52257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d510, d52257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51689 q = 1) (hb : d52336 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51689, d52336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro92 q ha hb
    | true =>
      simp only [d51689, d52336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro97 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52349 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d52350 q = 1) (hb : d58631 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52350, d58631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d52350, d58631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d52351 q = 1) (hb : d58632 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52351, d58632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d52351, d58632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d52352 q = 1) (hb : d58633 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52352, d58633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52352, d58633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4423 q = 1) (hb : d52356 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4423, d52356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4423, d52356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro80 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d52358 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4424 q = 1) (hb : d52359 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4424, d52359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4424, d52359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d4425 q = 1) (hb : d52360 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4425, d52360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4425, d52360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4426 q = 1) (hb : d52361 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4426, d52361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4426, d52361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d52362 q = 1) (hb : d58634 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52362, d58634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52362, d58634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d4433 q = 1) (hb : d52407 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4433, d52407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4433, d52407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro86 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d52414 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d4434 q = 1) (hb : d52415 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4434, d52415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d4434, d52415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d4435 q = 1) (hb : d52416 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4435, d52416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4435, d52416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d4436 q = 1) (hb : d52417 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4436, d52417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d4436, d52417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d4437 q = 1) (hb : d52418 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4437, d52418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d4437, d52418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d52419 q = 1) (hb : d58635 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d52419, d58635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d52419, d58635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
  exact h23 p ha hb
theorem andIntro4180 (p : Pattern) (ha : d52425 p = 1) (hb : d58641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52420 q = 1) (hb : d58636 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d52420, d58636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52420, d58636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4179 q ha hb
  have h2 (q : Pattern) (ha : d52421 q = 1) (hb : d58637 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d52421, d58637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52421, d58637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52422 q = 1) (hb : d58638 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d52422, d58638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52422, d58638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52423 q = 1) (hb : d58639 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d52423, d58639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52423, d58639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52424 q = 1) (hb : d58640 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d52424, d58640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52424, d58640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52425 q = 1) (hb : d58641 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d52425, d58641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52425, d58641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4181 (p : Pattern) (ha : d52656 p = 1) (hb : d58647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d790 q = 1) (hb : d52467 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d790, d52467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d790, d52467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108 q ha hb
  have h2 (q : Pattern) (ha : d791 q = 1) (hb : d52468 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d791, d52468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d791, d52468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d800 q = 1) (hb : d52477 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d52477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro108 q ha hb
    | true =>
      simp only [d800, d52477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro111 q ha hb
  have h4 (q : Pattern) (ha : d801 q = 1) (hb : d52478 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d52478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d801, d52478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d802 q = 1) (hb : d52479 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d802, d52479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d802, d52479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51715 q = 1) (hb : d52557 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51715, d52557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro139 q ha hb
    | true =>
      simp only [d51715, d52557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro144 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52570 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d52571 q = 1) (hb : d58643 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52571, d58643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d52571, d58643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d52572 q = 1) (hb : d58644 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52572, d58644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d52572, d58644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d52573 q = 1) (hb : d58645 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52573, d58645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52573, d58645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4461 q = 1) (hb : d52577 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4461, d52577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4461, d52577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro126 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d52579 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4462 q = 1) (hb : d52580 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4462, d52580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4462, d52580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d4463 q = 1) (hb : d52581 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4463, d52581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4463, d52581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4464 q = 1) (hb : d52582 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4464, d52582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4464, d52582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d52583 q = 1) (hb : d58646 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52583, d58646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52583, d58646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d4471 q = 1) (hb : d52644 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4471, d52644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4471, d52644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro133 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d52651 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d4472 q = 1) (hb : d52652 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4472, d52652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d4472, d52652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d4473 q = 1) (hb : d52653 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4473, d52653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4473, d52653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d4474 q = 1) (hb : d52654 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4474, d52654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d4474, d52654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d4475 q = 1) (hb : d52655 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4475, d52655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d4475, d52655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d52656 q = 1) (hb : d58647 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d52656, d58647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d52656, d58647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
  exact h23 p ha hb
theorem andIntro4182 (p : Pattern) (ha : d52662 p = 1) (hb : d58653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52657 q = 1) (hb : d58648 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d52657, d58648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52657, d58648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4181 q ha hb
  have h2 (q : Pattern) (ha : d52658 q = 1) (hb : d58649 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d52658, d58649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52658, d58649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52659 q = 1) (hb : d58650 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d52659, d58650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52659, d58650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52660 q = 1) (hb : d58651 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d52660, d58651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52660, d58651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52661 q = 1) (hb : d58652 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d52661, d58652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52661, d58652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52662 q = 1) (hb : d58653 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d52662, d58653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52662, d58653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4183 (p : Pattern) (ha : d52950 p = 1) (hb : d58660 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1169 q = 1) (hb : d52750 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1169, d52750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1169, d52750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro160 q ha hb
  have h2 (q : Pattern) (ha : d1170 q = 1) (hb : d52751 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1170, d52751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1170, d52751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1179 q = 1) (hb : d52760 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d52760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro160 q ha hb
    | true =>
      simp only [d1179, d52760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro163 q ha hb
  have h4 (q : Pattern) (ha : d1180 q = 1) (hb : d52761 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d52761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1180, d52761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1181 q = 1) (hb : d52762 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1181, d52762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1181, d52762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51742 q = 1) (hb : d52837 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51742, d52837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro191 q ha hb
    | true =>
      simp only [d51742, d52837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro196 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d52850 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d52851 q = 1) (hb : d58656 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d52851, d58656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d52851, d58656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d52852 q = 1) (hb : d58657 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d52852, d58657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d52852, d58657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d52853 q = 1) (hb : d58658 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d52853, d58658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d52853, d58658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4500 q = 1) (hb : d52857 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4500, d52857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4500, d52857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro178 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d52859 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4501 q = 1) (hb : d52860 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4501, d52860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4501, d52860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d4502 q = 1) (hb : d52861 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4502, d52861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4502, d52861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4503 q = 1) (hb : d52862 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4503, d52862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4503, d52862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d52863 q = 1) (hb : d58659 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d52863, d58659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d52863, d58659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d4510 q = 1) (hb : d52938 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4510, d52938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4510, d52938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro185 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d52945 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d4511 q = 1) (hb : d52946 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4511, d52946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d4511, d52946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d4512 q = 1) (hb : d52947 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4512, d52947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4512, d52947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d4513 q = 1) (hb : d52948 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4513, d52948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d4513, d52948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d4514 q = 1) (hb : d52949 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4514, d52949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d4514, d52949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d52950 q = 1) (hb : d58660 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d52950, d58660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d52950, d58660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
  exact h23 p ha hb
theorem andIntro4184 (p : Pattern) (ha : d52956 p = 1) (hb : d58666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d52951 q = 1) (hb : d58661 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d52951, d58661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52951, d58661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4183 q ha hb
  have h2 (q : Pattern) (ha : d52952 q = 1) (hb : d58662 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d52952, d58662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52952, d58662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d52953 q = 1) (hb : d58663 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d52953, d58663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52953, d58663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52954 q = 1) (hb : d58664 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d52954, d58664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52954, d58664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52955 q = 1) (hb : d58665 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d52955, d58665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52955, d58665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52956 q = 1) (hb : d58666 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d52956, d58666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52956, d58666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4185 (p : Pattern) (ha : d53265 p = 1) (hb : d58674 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1630 q = 1) (hb : d53071 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1630, d53071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1630, d53071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro218 q ha hb
  have h2 (q : Pattern) (ha : d1631 q = 1) (hb : d53072 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1631, d53072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1631, d53072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1640 q = 1) (hb : d53081 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d53081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro218 q ha hb
    | true =>
      simp only [d1640, d53081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro221 q ha hb
  have h4 (q : Pattern) (ha : d1641 q = 1) (hb : d53082 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d53082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1641, d53082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1642 q = 1) (hb : d53083 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1642, d53083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1642, d53083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51770 q = 1) (hb : d53152 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51770, d53152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro247 q ha hb
    | true =>
      simp only [d51770, d53152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro252 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d53165 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d53166 q = 1) (hb : d58670 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53166, d58670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d53166, d58670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d53167 q = 1) (hb : d58671 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53167, d58671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53167, d58671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d53168 q = 1) (hb : d58672 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53168, d58672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d53168, d58672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4540 q = 1) (hb : d53172 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4540, d53172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4540, d53172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro234 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d53174 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4541 q = 1) (hb : d53175 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4541, d53175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4541, d53175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d4542 q = 1) (hb : d53176 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4542, d53176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4542, d53176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4543 q = 1) (hb : d53177 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4543, d53177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4543, d53177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d53178 q = 1) (hb : d58673 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53178, d58673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53178, d58673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d4550 q = 1) (hb : d53253 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4550, d53253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4550, d53253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro241 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d53260 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d4551 q = 1) (hb : d53261 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4551, d53261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d4551, d53261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d4552 q = 1) (hb : d53262 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4552, d53262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4552, d53262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d4553 q = 1) (hb : d53263 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4553, d53263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d4553, d53263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d4554 q = 1) (hb : d53264 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4554, d53264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d4554, d53264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d53265 q = 1) (hb : d58674 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53265, d58674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d53265, d58674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
  exact h23 p ha hb
theorem andIntro4186 (p : Pattern) (ha : d53271 p = 1) (hb : d58680 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53266 q = 1) (hb : d58675 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53266, d58675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53266, d58675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4185 q ha hb
  have h2 (q : Pattern) (ha : d53267 q = 1) (hb : d58676 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53267, d58676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53267, d58676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53268 q = 1) (hb : d58677 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53268, d58677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53268, d58677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53269 q = 1) (hb : d58678 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53269, d58678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53269, d58678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53270 q = 1) (hb : d58679 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53270, d58679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53270, d58679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53271 q = 1) (hb : d58680 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53271, d58680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53271, d58680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4187 (p : Pattern) (ha : d53582 p = 1) (hb : d58689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2113 q = 1) (hb : d53392 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2113, d53392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2113, d53392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro277 q ha hb
  have h2 (q : Pattern) (ha : d2114 q = 1) (hb : d53393 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2114, d53393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2114, d53393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2123 q = 1) (hb : d53402 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d53402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro277 q ha hb
    | true =>
      simp only [d2123, d53402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro280 q ha hb
  have h4 (q : Pattern) (ha : d2124 q = 1) (hb : d53403 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d53403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2124, d53403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2125 q = 1) (hb : d53404 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2125, d53404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2125, d53404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51799 q = 1) (hb : d53469 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51799, d53469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro306 q ha hb
    | true =>
      simp only [d51799, d53469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro311 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d53482 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d53483 q = 1) (hb : d58685 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53483, d58685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d53483, d58685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d53484 q = 1) (hb : d58686 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53484, d58686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d53484, d58686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d53485 q = 1) (hb : d58687 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53485, d58687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d53485, d58687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d4581 q = 1) (hb : d53489 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4581, d53489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4581, d53489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro293 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d53491 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d4582 q = 1) (hb : d53492 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4582, d53492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d4582, d53492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d4583 q = 1) (hb : d53493 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4583, d53493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4583, d53493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d4584 q = 1) (hb : d53494 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4584, d53494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4584, d53494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d53495 q = 1) (hb : d58688 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53495, d58688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53495, d58688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d4591 q = 1) (hb : d53570 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4591, d53570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4591, d53570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro300 q ha hb
  have h18 (q : Pattern) (ha : d0 q = 1) (hb : d53577 q = 1) : d0 q = 1 := by
    exact ha
  have h19 (q : Pattern) (ha : d4592 q = 1) (hb : d53578 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4592, d53578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d4592, d53578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d4593 q = 1) (hb : d53579 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4593, d53579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4593, d53579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d4594 q = 1) (hb : d53580 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4594, d53580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d4594, d53580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d4595 q = 1) (hb : d53581 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4595, d53581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d4595, d53581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d53582 q = 1) (hb : d58689 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d53582, d58689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d53582, d58689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
  exact h23 p ha hb
theorem andIntro4188 (p : Pattern) (ha : d53588 p = 1) (hb : d58695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53583 q = 1) (hb : d58690 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53583, d58690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53583, d58690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4187 q ha hb
  have h2 (q : Pattern) (ha : d53584 q = 1) (hb : d58691 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53584, d58691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53584, d58691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53585 q = 1) (hb : d58692 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53585, d58692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53585, d58692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53586 q = 1) (hb : d58693 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53586, d58693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53586, d58693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53587 q = 1) (hb : d58694 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53587, d58694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53587, d58694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53588 q = 1) (hb : d58695 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d53588, d58695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d53588, d58695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4189 (p : Pattern) (ha : d53594 p = 1) (hb : d58701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d52426 q = 1) (hb : d58642 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d52426, d58642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4178 q ha hb
    | true =>
      simp only [d52426, d58642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4180 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52663 q = 1) (hb : d58654 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d52663, d58654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52663, d58654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4182 q ha hb
  have h3 (q : Pattern) (ha : d52664 q = 1) (hb : d58655 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d52664, d58655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d52664, d58655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52957 q = 1) (hb : d58667 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d52957, d58667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52957, d58667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4184 q ha hb
  have h5 (q : Pattern) (ha : d52958 q = 1) (hb : d58668 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d52958, d58668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52958, d58668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52959 q = 1) (hb : d58669 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d52959, d58669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d52959, d58669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d53272 q = 1) (hb : d58681 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53272, d58681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53272, d58681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4186 q ha hb
  have h8 (q : Pattern) (ha : d53273 q = 1) (hb : d58682 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53273, d58682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53273, d58682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d53274 q = 1) (hb : d58683 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53274, d58683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53274, d58683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d53275 q = 1) (hb : d58684 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53275, d58684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53275, d58684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d53589 q = 1) (hb : d58696 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d53589, d58696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53589, d58696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4188 q ha hb
  have h12 (q : Pattern) (ha : d53590 q = 1) (hb : d58697 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d53590, d58697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53590, d58697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d53591 q = 1) (hb : d58698 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d53591, d58698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53591, d58698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d53592 q = 1) (hb : d58699 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d53592, d58699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d53592, d58699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d53593 q = 1) (hb : d58700 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d53593, d58700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53593, d58700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d53594 q = 1) (hb : d58701 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d53594, d58701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d53594, d58701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro4190 (p : Pattern) (ha : d53600 p = 1) (hb : d58707 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53595 q = 1) (hb : d58702 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d53595, d58702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4189 q ha hb
    | true =>
      simp only [d53595, d58702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53596 q = 1) (hb : d58703 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d53596, d58703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53596, d58703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d53597 q = 1) (hb : d58704 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d53597, d58704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53597, d58704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53598 q = 1) (hb : d58705 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d53598, d58705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53598, d58705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53599 q = 1) (hb : d58706 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d53599, d58706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53599, d58706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53600 q = 1) (hb : d58707 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d53600, d58707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53600, d58707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4191 (p : Pattern) (ha : d53606 p = 1) (hb : d58713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53601 q = 1) (hb : d58708 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d53601, d58708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4190 q ha hb
    | true =>
      simp only [d53601, d58708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53602 q = 1) (hb : d58709 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d53602, d58709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53602, d58709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d53603 q = 1) (hb : d58710 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d53603, d58710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53603, d58710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53604 q = 1) (hb : d58711 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d53604, d58711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53604, d58711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53605 q = 1) (hb : d58712 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d53605, d58712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53605, d58712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53606 q = 1) (hb : d58713 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d53606, d58713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53606, d58713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4192 (p : Pattern) (ha : d53612 p = 1) (hb : d58719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53607 q = 1) (hb : d58714 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d53607, d58714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4191 q ha hb
    | true =>
      simp only [d53607, d58714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53608 q = 1) (hb : d58715 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d53608, d58715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53608, d58715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d53609 q = 1) (hb : d58716 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d53609, d58716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53609, d58716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53610 q = 1) (hb : d58717 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d53610, d58717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53610, d58717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53611 q = 1) (hb : d58718 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d53611, d58718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53611, d58718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53612 q = 1) (hb : d58719 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d53612, d58719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53612, d58719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4193 (p : Pattern) (ha : d53618 p = 1) (hb : d58725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53613 q = 1) (hb : d58720 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d53613, d58720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4192 q ha hb
    | true =>
      simp only [d53613, d58720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53614 q = 1) (hb : d58721 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d53614, d58721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53614, d58721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d53615 q = 1) (hb : d58722 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d53615, d58722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53615, d58722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53616 q = 1) (hb : d58723 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d53616, d58723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53616, d58723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53617 q = 1) (hb : d58724 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d53617, d58724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53617, d58724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53618 q = 1) (hb : d58725 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d53618, d58725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53618, d58725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4194 (p : Pattern) (ha : d53624 p = 1) (hb : d58731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53619 q = 1) (hb : d58726 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d53619, d58726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4193 q ha hb
    | true =>
      simp only [d53619, d58726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53620 q = 1) (hb : d58727 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d53620, d58727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53620, d58727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d53621 q = 1) (hb : d58728 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d53621, d58728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53621, d58728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53622 q = 1) (hb : d58729 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d53622, d58729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53622, d58729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53623 q = 1) (hb : d58730 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d53623, d58730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53623, d58730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53624 q = 1) (hb : d58731 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d53624, d58731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53624, d58731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4195 (p : Pattern) (ha : d53630 p = 1) (hb : d58737 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53625 q = 1) (hb : d58732 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d53625, d58732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4194 q ha hb
    | true =>
      simp only [d53625, d58732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53626 q = 1) (hb : d58733 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d53626, d58733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53626, d58733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d53627 q = 1) (hb : d58734 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d53627, d58734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53627, d58734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53628 q = 1) (hb : d58735 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d53628, d58735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53628, d58735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53629 q = 1) (hb : d58736 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d53629, d58736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53629, d58736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53630 q = 1) (hb : d58737 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d53630, d58737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53630, d58737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4196 (p : Pattern) (ha : d53636 p = 1) (hb : d58743 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53631 q = 1) (hb : d58738 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d53631, d58738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4195 q ha hb
    | true =>
      simp only [d53631, d58738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53632 q = 1) (hb : d58739 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d53632, d58739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53632, d58739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d53633 q = 1) (hb : d58740 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d53633, d58740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53633, d58740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53634 q = 1) (hb : d58741 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d53634, d58741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d53634, d58741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53635 q = 1) (hb : d58742 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d53635, d58742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53635, d58742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d53636 q = 1) (hb : d58743 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d53636, d58743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53636, d58743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro4197 (p : Pattern) (ha : d53869 p = 1) (hb : d58737 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53867 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53869 q = 1) (hb : d58736 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d53869, d58736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53869, d58736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d53869 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d53869 q = 1) (hb : d58737 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d58737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  exact h4 p ha hb
theorem andIntro4198 (p : Pattern) (ha : d53870 p = 1) (hb : d58743 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53869 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53869 q = 1) (hb : d58738 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d58738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4197 q ha hb
    | true =>
      simp only [d58738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d53869 q = 1) (hb : d58739 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d58739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d53869 q = 1) (hb : d58740 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d58740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d58740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d53869 q = 1) (hb : d58741 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d58741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d53869 q = 1) (hb : d58742 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d58742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d58742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d53870 q = 1) (hb : d58743 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d53870, d58743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53870, d58743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro4199 (p : Pattern) (ha : d4349 p = 1) (hb : d58747 p = 1) : d69447 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d203 q = 1) : d203 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d49 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d204 q = 1) (hb : d58747 q = 1) : d390 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d58747, d390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d204, d58747, d390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4340 q = 1) (hb : d58747 q = 1) : d391 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4340, d391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d51 q = 1) (hb : d58747 q = 1) : d51 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d4341 q = 1) (hb : d58747 q = 1) : d69437 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d69437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4341, d69437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4342 q = 1) (hb : d58747 q = 1) : d69445 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4342, d69445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4342, d69445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4343 q = 1) (hb : d58747 q = 1) : d69446 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4343, d69446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4343, d69446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4349 q = 1) (hb : d58747 q = 1) : d69447 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4349, d69447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4349, d69447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro4200 (p : Pattern) (ha : d4359 p = 1) (hb : d58747 p = 1) : d69456 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d243 q = 1) : d243 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d83 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d244 q = 1) (hb : d58747 q = 1) : d451 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d58747, d451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d244, d58747, d451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4355 q = 1) (hb : d58747 q = 1) : d452 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4355, d452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4355, d452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d85 q = 1) (hb : d58747 q = 1) : d85 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d4356 q = 1) (hb : d58747 q = 1) : d69453 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4356, d69453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4356, d69453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4357 q = 1) (hb : d58747 q = 1) : d69454 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4357, d69454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4357, d69454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4358 q = 1) (hb : d58747 q = 1) : d69455 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4358, d69455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4358, d69455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4359 q = 1) (hb : d58747 q = 1) : d69456 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4359, d69456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4359, d69456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro4201 (p : Pattern) (ha : d51643 p = 1) (hb : d58747 p = 1) : d69436 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d58747 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d58747 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1 q = 1) (hb : d156 q = 1) : d156 q = 1 := by
    exact hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d42 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d157 q = 1) (hb : d58747 q = 1) : d370 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d58747, d370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d157, d58747, d370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d4335 q = 1) (hb : d58747 q = 1) : d371 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4335, d371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d44 q = 1) (hb : d58747 q = 1) : d44 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d4336 q = 1) (hb : d58747 q = 1) : d69433 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d69433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4336, d69433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51641 q = 1) (hb : d58747 q = 1) : d69434 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d69434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51641, d69434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d51642 q = 1) (hb : d58747 q = 1) : d69435 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d69435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51642, d69435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d51643 q = 1) (hb : d58747 q = 1) : d69436 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51643, d69436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51643, d69436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro4202 (p : Pattern) (ha : d51646 p = 1) (hb : d58747 p = 1) : d69440 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d58747 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d58747 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1 q = 1) (hb : d156 q = 1) : d156 q = 1 := by
    exact hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d42 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d157 q = 1) (hb : d58747 q = 1) : d370 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d58747, d370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d157, d58747, d370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d4335 q = 1) (hb : d58747 q = 1) : d371 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4335, d371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d44 q = 1) (hb : d58747 q = 1) : d44 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d4336 q = 1) (hb : d58747 q = 1) : d69433 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d69433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d4336, d69433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51641 q = 1) (hb : d58747 q = 1) : d69434 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d69434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51641, d69434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d51642 q = 1) (hb : d58747 q = 1) : d69435 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d69435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51642, d69435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d198 q = 1) (hb : d58747 q = 1) : d198 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d202 q = 1) (hb : d58747 q = 1) : d202 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d1 q = 1) (hb : d203 q = 1) : d203 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d49 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d204 q = 1) (hb : d58747 q = 1) : d390 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d58747, d390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d204, d58747, d390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d4340 q = 1) (hb : d58747 q = 1) : d391 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4340, d391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h17 (q : Pattern) (ha : d51 q = 1) (hb : d58747 q = 1) : d51 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d4341 q = 1) (hb : d58747 q = 1) : d69437 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d69437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d4341, d69437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d51644 q = 1) (hb : d58747 q = 1) : d69438 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51644, d69438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d51644, d69438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d51645 q = 1) (hb : d58747 q = 1) : d69439 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51645, d69439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51645, d69439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d51646 q = 1) (hb : d58747 q = 1) : d69440 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51646, d69440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51646, d69440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro4203 (p : Pattern) (ha : d58614 p = 1) (hb : d68751 p = 1) : d69462 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d68751 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51647 q = 1) (hb : d58747 q = 1) : d69441 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51647, d69441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4201 q ha hb
    | true =>
      simp only [d51647, d69441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4202 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d58610 q = 1) (hb : d68751 q = 1) : d69442 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58610, d68751, d69442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58610, d68751, d69442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d68751 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d58611 q = 1) (hb : d68751 q = 1) : d69443 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58611, d69443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d58611, d69443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58612 q = 1) (hb : d68751 q = 1) : d69444 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58612, d69444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58612, d69444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d4350 q = 1) (hb : d58747 q = 1) : d69448 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4350, d69448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4350, d69448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4199 q ha hb
  have h9 (q : Pattern) (ha : d4351 q = 1) (hb : d68751 q = 1) : d69449 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4351, d68751, d69449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4351, d68751, d69449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d4352 q = 1) (hb : d68751 q = 1) : d69450 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4352, d69450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4352, d69450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d4353 q = 1) (hb : d68751 q = 1) : d69451 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4353, d69451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d4353, d69451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d58613 q = 1) (hb : d68751 q = 1) : d69452 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58613, d69452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58613, d69452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d4360 q = 1) (hb : d58747 q = 1) : d69457 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4360, d69457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4360, d69457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4200 q ha hb
  have h14 (q : Pattern) (ha : d4361 q = 1) (hb : d68751 q = 1) : d69458 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4361, d68751, d69458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4361, d68751, d69458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h15 (q : Pattern) (ha : d4362 q = 1) (hb : d68751 q = 1) : d69459 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4362, d69459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4362, d69459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d4363 q = 1) (hb : d68751 q = 1) : d69460 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4363, d69460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4363, d69460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d4364 q = 1) (hb : d68751 q = 1) : d69461 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4364, d69461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d4364, d69461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d58614 q = 1) (hb : d68751 q = 1) : d69462 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58614, d69462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d58614, d69462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro4204 (p : Pattern) (ha : d284 p = 1) (hb : d58747 p = 1) : d4693 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d156 q = 1) : d156 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d157 q = 1) (hb : d58747 q = 1) : d370 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d58747, d370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d157, d58747, d370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d280 q = 1) (hb : d58747 q = 1) : d4689 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d4689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d4689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d281 q = 1) (hb : d58747 q = 1) : d4690 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d4690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d281, d4690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d282 q = 1) (hb : d58747 q = 1) : d4691 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d4691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d4691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d283 q = 1) (hb : d58747 q = 1) : d4692 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d4692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d4692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d284 q = 1) (hb : d58747 q = 1) : d4693 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d284, d4693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d284, d4693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4205 (p : Pattern) (ha : d291 p = 1) (hb : d58747 p = 1) : d4700 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d156 q = 1) : d156 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d42 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d157 q = 1) (hb : d58747 q = 1) : d370 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d58747, d370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d157, d58747, d370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d280 q = 1) (hb : d58747 q = 1) : d4689 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d4689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d4689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d281 q = 1) (hb : d58747 q = 1) : d4690 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d4690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d281, d4690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d282 q = 1) (hb : d58747 q = 1) : d4691 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d4691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d4691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d283 q = 1) (hb : d58747 q = 1) : d4692 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d4692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d4692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d203 q = 1) : d203 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d49 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d204 q = 1) (hb : d58747 q = 1) : d390 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d58747, d390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d204, d58747, d390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d287 q = 1) (hb : d58747 q = 1) : d4696 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d4696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287, d4696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d288 q = 1) (hb : d58747 q = 1) : d4697 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d4697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d288, d4697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d289 q = 1) (hb : d58747 q = 1) : d4698 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d4698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d4698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d290 q = 1) (hb : d58747 q = 1) : d4699 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d4699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d4699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d291 q = 1) (hb : d58747 q = 1) : d4700 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291, d4700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d291, d4700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro4206 (p : Pattern) (ha : d4385 p = 1) (hb : d58747 p = 1) : d69484 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d385 q = 1) : d385 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d203 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d386 q = 1) (hb : d58747 q = 1) : d4725 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d386, d58747, d4725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d386, d58747, d4725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4376 q = 1) (hb : d58747 q = 1) : d69473 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4376, d69473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4376, d69473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d391 q = 1) (hb : d58747 q = 1) : d391 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d4377 q = 1) (hb : d58747 q = 1) : d69474 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4377, d69474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4377, d69474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4378 q = 1) (hb : d58747 q = 1) : d69482 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4378, d69482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4378, d69482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4379 q = 1) (hb : d58747 q = 1) : d69483 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4379, d69483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4379, d69483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4385 q = 1) (hb : d58747 q = 1) : d69484 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4385, d69484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4385, d69484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro4207 (p : Pattern) (ha : d4395 p = 1) (hb : d58747 p = 1) : d69494 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d429 q = 1) : d429 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d243 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d430 q = 1) (hb : d58747 q = 1) : d4755 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d430, d58747, d4755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d430, d58747, d4755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4391 q = 1) (hb : d58747 q = 1) : d69490 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4391, d69490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4391, d69490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d452 q = 1) (hb : d58747 q = 1) : d452 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d4392 q = 1) (hb : d58747 q = 1) : d69491 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4392, d69491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4392, d69491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4393 q = 1) (hb : d58747 q = 1) : d69492 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4393, d69492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4393, d69492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4394 q = 1) (hb : d58747 q = 1) : d69493 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4394, d69493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4394, d69493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4395 q = 1) (hb : d58747 q = 1) : d69494 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4395, d69494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4395, d69494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro4208 (p : Pattern) (ha : d51660 p = 1) (hb : d58747 p = 1) : d69472 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d296 q = 1) : d296 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d116 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d297 q = 1) (hb : d58747 q = 1) : d4704 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d58747, d4704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d297, d58747, d4704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d298 q = 1) (hb : d58747 q = 1) : d4705 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d4705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d4705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d299 q = 1) (hb : d58747 q = 1) : d4706 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d4706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d299, d4706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d300 q = 1) (hb : d58747 q = 1) : d4707 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d4707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d4707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d303 q = 1) : d303 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d123 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d304 q = 1) (hb : d58747 q = 1) : d4708 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d58747, d4708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d304, d58747, d4708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d305 q = 1) (hb : d58747 q = 1) : d4709 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d4709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d4709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d306 q = 1) (hb : d58747 q = 1) : d4710 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d4710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d306, d4710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d1 q = 1) (hb : d336 q = 1) : d336 q = 1 := by
    exact hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d156 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d337 q = 1) (hb : d58747 q = 1) : d4711 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d337, d58747, d4711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d337, d58747, d4711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d4371 q = 1) (hb : d58747 q = 1) : d69468 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4371, d69468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4371, d69468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d371 q = 1) (hb : d58747 q = 1) : d371 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d4372 q = 1) (hb : d58747 q = 1) : d69469 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4372, d69469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4372, d69469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d51658 q = 1) (hb : d58747 q = 1) : d69470 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51658, d69470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51658, d69470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d51659 q = 1) (hb : d58747 q = 1) : d69471 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51659, d69471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51659, d69471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d51660 q = 1) (hb : d58747 q = 1) : d69472 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51660, d69472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51660, d69472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro4209 (p : Pattern) (ha : d51663 p = 1) (hb : d58747 p = 1) : d69477 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d296 q = 1) : d296 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d116 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d297 q = 1) (hb : d58747 q = 1) : d4704 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d58747, d4704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d297, d58747, d4704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d298 q = 1) (hb : d58747 q = 1) : d4705 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d4705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d4705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d299 q = 1) (hb : d58747 q = 1) : d4706 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d4706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d299, d4706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d300 q = 1) (hb : d58747 q = 1) : d4707 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d4707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d4707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d303 q = 1) : d303 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d123 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d304 q = 1) (hb : d58747 q = 1) : d4708 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d58747, d4708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d304, d58747, d4708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d305 q = 1) (hb : d58747 q = 1) : d4709 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d4709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d4709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d306 q = 1) (hb : d58747 q = 1) : d4710 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d4710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d306, d4710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d1 q = 1) (hb : d336 q = 1) : d336 q = 1 := by
    exact hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d156 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d337 q = 1) (hb : d58747 q = 1) : d4711 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d337, d58747, d4711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d337, d58747, d4711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d4371 q = 1) (hb : d58747 q = 1) : d69468 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4371, d69468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4371, d69468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d371 q = 1) (hb : d58747 q = 1) : d371 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d4372 q = 1) (hb : d58747 q = 1) : d69469 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4372, d69469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4372, d69469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d51658 q = 1) (hb : d58747 q = 1) : d69470 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51658, d69470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51658, d69470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d51659 q = 1) (hb : d58747 q = 1) : d69471 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51659, d69471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51659, d69471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d1 q = 1) (hb : d376 q = 1) : d376 q = 1 := by
    exact hb
  have h21 (q : Pattern) (ha : d0 q = 1) (hb : d194 q = 1) : d0 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d377 q = 1) (hb : d58747 q = 1) : d4718 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377, d58747, d4718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
    | true =>
      simp only [d377, d58747, d4718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
  have h23 (q : Pattern) (ha : d378 q = 1) (hb : d58747 q = 1) : d4719 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d378, d4719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d378, d4719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d379 q = 1) (hb : d58747 q = 1) : d4720 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d379, d4720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d379, d4720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d380 q = 1) (hb : d58747 q = 1) : d4721 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d380, d4721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d380, d4721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d1 q = 1) (hb : d381 q = 1) : d381 q = 1 := by
    exact hb
  have h27 (q : Pattern) (ha : d0 q = 1) (hb : d199 q = 1) : d0 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d382 q = 1) (hb : d58747 q = 1) : d4722 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d382, d58747, d4722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
    | true =>
      simp only [d382, d58747, d4722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d383 q = 1) (hb : d58747 q = 1) : d4723 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d383, d4723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d383, d4723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d384 q = 1) (hb : d58747 q = 1) : d4724 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d384, d4724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
    | true =>
      simp only [d384, d4724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h31 (q : Pattern) (ha : d1 q = 1) (hb : d385 q = 1) : d385 q = 1 := by
    exact hb
  have h32 (q : Pattern) (ha : d0 q = 1) (hb : d203 q = 1) : d0 q = 1 := by
    exact ha
  have h33 (q : Pattern) (ha : d386 q = 1) (hb : d58747 q = 1) : d4725 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d386, d58747, d4725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q hb ha
    | true =>
      simp only [d386, d58747, d4725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q hb ha
  have h34 (q : Pattern) (ha : d4376 q = 1) (hb : d58747 q = 1) : d69473 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4376, d69473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
    | true =>
      simp only [d4376, d69473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h35 (q : Pattern) (ha : d391 q = 1) (hb : d58747 q = 1) : d391 q = 1 := by
    exact ha
  have h36 (q : Pattern) (ha : d4377 q = 1) (hb : d58747 q = 1) : d69474 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4377, d69474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
    | true =>
      simp only [d4377, d69474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h35 q ha hb
  have h37 (q : Pattern) (ha : d51661 q = 1) (hb : d58747 q = 1) : d69475 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51661, d69475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
    | true =>
      simp only [d51661, d69475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h36 q ha hb
  have h38 (q : Pattern) (ha : d51662 q = 1) (hb : d58747 q = 1) : d69476 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51662, d69476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d51662, d69476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h37 q ha hb
  have h39 (q : Pattern) (ha : d51663 q = 1) (hb : d58747 q = 1) : d69477 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51663, d69477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d51663, d69477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h38 q ha hb
  exact h39 p ha hb
theorem andIntro4210 (p : Pattern) (ha : d58624 p = 1) (hb : d68751 p = 1) : d69500 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285 q = 1) (hb : d58747 q = 1) : d4694 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, d4694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, d4694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4204 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d286 q = 1) (hb : d68751 q = 1) : d4695 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, d68751, d4695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286, d68751, d4695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d292 q = 1) (hb : d58747 q = 1) : d4701 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d4701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4204 q ha hb
    | true =>
      simp only [d292, d4701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4205 q ha hb
  have h5 (q : Pattern) (ha : d293 q = 1) (hb : d68751 q = 1) : d4702 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d68751, d4702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d293, d68751, d4702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d294 q = 1) (hb : d68751 q = 1) : d4703 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, d4703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d294, d4703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51664 q = 1) (hb : d58747 q = 1) : d69478 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51664, d69478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4208 q ha hb
    | true =>
      simp only [d51664, d69478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4209 q ha hb
  have h8 (q : Pattern) (ha : d58620 q = 1) (hb : d68751 q = 1) : d69479 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58620, d68751, d69479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d58620, d68751, d69479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d68751 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d58621 q = 1) (hb : d68751 q = 1) : d69480 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58621, d69480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58621, d69480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d58622 q = 1) (hb : d68751 q = 1) : d69481 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58622, d69481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58622, d69481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4386 q = 1) (hb : d58747 q = 1) : d69485 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4386, d69485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4386, d69485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4206 q ha hb
  have h13 (q : Pattern) (ha : d4387 q = 1) (hb : d68751 q = 1) : d69486 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4387, d68751, d69486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4387, d68751, d69486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d4388 q = 1) (hb : d68751 q = 1) : d69487 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4388, d69487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4388, d69487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h15 (q : Pattern) (ha : d4389 q = 1) (hb : d68751 q = 1) : d69488 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4389, d69488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4389, d69488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h16 (q : Pattern) (ha : d58623 q = 1) (hb : d68751 q = 1) : d69489 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58623, d69489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d58623, d69489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d4396 q = 1) (hb : d58747 q = 1) : d69495 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4396, d69495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4396, d69495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4207 q ha hb
  have h18 (q : Pattern) (ha : d4397 q = 1) (hb : d68751 q = 1) : d69496 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4397, d68751, d69496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d4397, d68751, d69496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h19 (q : Pattern) (ha : d4398 q = 1) (hb : d68751 q = 1) : d69497 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4398, d69497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d4398, d69497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h20 (q : Pattern) (ha : d4399 q = 1) (hb : d68751 q = 1) : d69498 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4399, d69498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4399, d69498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h21 (q : Pattern) (ha : d4400 q = 1) (hb : d68751 q = 1) : d69499 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4400, d69499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d4400, d69499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h22 (q : Pattern) (ha : d58624 q = 1) (hb : d68751 q = 1) : d69500 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58624, d69500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d58624, d69500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro4211 (p : Pattern) (ha : d58630 p = 1) (hb : d68751 p = 1) : d69506 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d68751 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d68751 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d58615 q = 1) (hb : d68751 q = 1) : d69463 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58615, d69463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58615, d69463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4203 q ha hb
  have h3 (q : Pattern) (ha : d58616 q = 1) (hb : d68751 q = 1) : d69464 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58616, d69464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58616, d69464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58617 q = 1) (hb : d68751 q = 1) : d69465 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58617, d69465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58617, d69465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58618 q = 1) (hb : d68751 q = 1) : d69466 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58618, d69466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58618, d69466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58619 q = 1) (hb : d68751 q = 1) : d69467 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58619, d69467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58619, d69467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d58625 q = 1) (hb : d68751 q = 1) : d69501 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58625, d69501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58625, d69501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4210 q ha hb
  have h8 (q : Pattern) (ha : d58626 q = 1) (hb : d68751 q = 1) : d69502 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58626, d69502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58626, d69502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d58627 q = 1) (hb : d68751 q = 1) : d69503 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58627, d69503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58627, d69503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d58628 q = 1) (hb : d68751 q = 1) : d69504 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58628, d69504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58628, d69504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d58629 q = 1) (hb : d68751 q = 1) : d69505 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58629, d69505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d58629, d69505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d58630 q = 1) (hb : d68751 q = 1) : d69506 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58630, d69506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58630, d69506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro4212 (p : Pattern) (ha : d497 p = 1) (hb : d58747 p = 1) : d4778 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d487 q = 1) : d487 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d491 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d492 q = 1) (hb : d58747 q = 1) : d603 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d492, d58747, d603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d492, d58747, d603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d493 q = 1) (hb : d58747 q = 1) : d4774 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, d4774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d493, d4774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d494 q = 1) (hb : d58747 q = 1) : d4775 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, d4775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d494, d4775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d495 q = 1) (hb : d58747 q = 1) : d4776 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, d4776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d495, d4776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d496 q = 1) (hb : d58747 q = 1) : d4777 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, d4777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, d4777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d497 q = 1) (hb : d58747 q = 1) : d4778 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d497, d4778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d497, d4778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4213 (p : Pattern) (ha : d507 p = 1) (hb : d58747 p = 1) : d4785 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d487 q = 1) : d487 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d491 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d492 q = 1) (hb : d58747 q = 1) : d603 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d492, d58747, d603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d492, d58747, d603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d493 q = 1) (hb : d58747 q = 1) : d4774 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d493, d4774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d493, d4774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d494 q = 1) (hb : d58747 q = 1) : d4775 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d494, d4775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d494, d4775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d495 q = 1) (hb : d58747 q = 1) : d4776 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d495, d4776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d495, d4776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d496 q = 1) (hb : d58747 q = 1) : d4777 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d496, d4777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d496, d4777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d500 q = 1) : d500 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d501 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d502 q = 1) (hb : d58747 q = 1) : d626 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d502, d58747, d626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d502, d58747, d626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d503 q = 1) (hb : d58747 q = 1) : d4781 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d503, d4781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d503, d4781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d504 q = 1) (hb : d58747 q = 1) : d4782 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d504, d4782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d504, d4782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d505 q = 1) (hb : d58747 q = 1) : d4783 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d505, d4783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d505, d4783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d506 q = 1) (hb : d58747 q = 1) : d4784 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d506, d4784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d506, d4784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d507 q = 1) (hb : d58747 q = 1) : d4785 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d507, d4785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d507, d4785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro4214 (p : Pattern) (ha : d4422 p = 1) (hb : d58747 p = 1) : d69523 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d620 q = 1) : d620 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d500 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d621 q = 1) (hb : d58747 q = 1) : d4810 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d621, d58747, d4810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d621, d58747, d4810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4413 q = 1) (hb : d58747 q = 1) : d69512 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4413, d69512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4413, d69512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d627 q = 1) (hb : d58747 q = 1) : d627 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d4414 q = 1) (hb : d58747 q = 1) : d69513 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4414, d69513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4414, d69513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4415 q = 1) (hb : d58747 q = 1) : d69521 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4415, d69521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4415, d69521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4416 q = 1) (hb : d58747 q = 1) : d69522 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4416, d69522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4416, d69522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4422 q = 1) (hb : d58747 q = 1) : d69523 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4422, d69523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4422, d69523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro4215 (p : Pattern) (ha : d4432 p = 1) (hb : d58747 p = 1) : d69533 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d681 q = 1) : d681 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d689 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d690 q = 1) (hb : d58747 q = 1) : d4849 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d690, d58747, d4849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d690, d58747, d4849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4428 q = 1) (hb : d58747 q = 1) : d69529 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4428, d69529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4428, d69529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d721 q = 1) (hb : d58747 q = 1) : d721 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d4429 q = 1) (hb : d58747 q = 1) : d69530 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4429, d69530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4429, d69530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4430 q = 1) (hb : d58747 q = 1) : d69531 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4430, d69531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4430, d69531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4431 q = 1) (hb : d58747 q = 1) : d69532 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4431, d69532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4431, d69532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4432 q = 1) (hb : d58747 q = 1) : d69533 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4432, d69533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4432, d69533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro4216 (p : Pattern) (ha : d51685 p = 1) (hb : d58747 p = 1) : d69511 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d512 q = 1) : d512 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d514 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d515 q = 1) (hb : d58747 q = 1) : d4789 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d515, d58747, d4789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d515, d58747, d4789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d516 q = 1) (hb : d58747 q = 1) : d4790 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d516, d4790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d516, d4790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d517 q = 1) (hb : d58747 q = 1) : d4791 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d517, d4791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d517, d4791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d518 q = 1) (hb : d58747 q = 1) : d4792 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d518, d4792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d518, d4792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d521 q = 1) : d521 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d524 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d525 q = 1) (hb : d58747 q = 1) : d4793 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d525, d58747, d4793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d525, d58747, d4793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d526 q = 1) (hb : d58747 q = 1) : d4794 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d526, d4794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d526, d4794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d527 q = 1) (hb : d58747 q = 1) : d4795 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d527, d4795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d527, d4795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d1 q = 1) (hb : d560 q = 1) : d560 q = 1 := by
    exact hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d487 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d561 q = 1) (hb : d58747 q = 1) : d4796 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d561, d58747, d4796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d561, d58747, d4796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d4408 q = 1) (hb : d58747 q = 1) : d69507 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4408, d69507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4408, d69507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d604 q = 1) (hb : d58747 q = 1) : d604 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d4409 q = 1) (hb : d58747 q = 1) : d69508 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4409, d69508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4409, d69508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d51683 q = 1) (hb : d58747 q = 1) : d69509 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51683, d69509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51683, d69509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d51684 q = 1) (hb : d58747 q = 1) : d69510 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51684, d69510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51684, d69510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d51685 q = 1) (hb : d58747 q = 1) : d69511 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51685, d69511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51685, d69511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro4217 (p : Pattern) (ha : d51688 p = 1) (hb : d58747 p = 1) : d69516 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d512 q = 1) : d512 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d514 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d515 q = 1) (hb : d58747 q = 1) : d4789 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d515, d58747, d4789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d515, d58747, d4789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d516 q = 1) (hb : d58747 q = 1) : d4790 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d516, d4790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d516, d4790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d517 q = 1) (hb : d58747 q = 1) : d4791 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d517, d4791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d517, d4791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d518 q = 1) (hb : d58747 q = 1) : d4792 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d518, d4792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d518, d4792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d521 q = 1) : d521 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d524 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d525 q = 1) (hb : d58747 q = 1) : d4793 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d525, d58747, d4793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d525, d58747, d4793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d526 q = 1) (hb : d58747 q = 1) : d4794 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d526, d4794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d526, d4794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d527 q = 1) (hb : d58747 q = 1) : d4795 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d527, d4795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d527, d4795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d1 q = 1) (hb : d560 q = 1) : d560 q = 1 := by
    exact hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d487 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d561 q = 1) (hb : d58747 q = 1) : d4796 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d561, d58747, d4796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d561, d58747, d4796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d4408 q = 1) (hb : d58747 q = 1) : d69507 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4408, d69507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4408, d69507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d604 q = 1) (hb : d58747 q = 1) : d604 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d4409 q = 1) (hb : d58747 q = 1) : d69508 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4409, d69508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4409, d69508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d51683 q = 1) (hb : d58747 q = 1) : d69509 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51683, d69509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51683, d69509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d51684 q = 1) (hb : d58747 q = 1) : d69510 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51684, d69510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51684, d69510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d1 q = 1) (hb : d609 q = 1) : d609 q = 1 := by
    exact hb
  have h21 (q : Pattern) (ha : d0 q = 1) (hb : d610 q = 1) : d0 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d611 q = 1) (hb : d58747 q = 1) : d4803 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d611, d58747, d4803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
    | true =>
      simp only [d611, d58747, d4803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
  have h23 (q : Pattern) (ha : d612 q = 1) (hb : d58747 q = 1) : d4804 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d612, d4804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d612, d4804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d613 q = 1) (hb : d58747 q = 1) : d4805 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d613, d4805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d613, d4805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d614 q = 1) (hb : d58747 q = 1) : d4806 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d614, d4806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d614, d4806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d1 q = 1) (hb : d615 q = 1) : d615 q = 1 := by
    exact hb
  have h27 (q : Pattern) (ha : d0 q = 1) (hb : d616 q = 1) : d0 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d617 q = 1) (hb : d58747 q = 1) : d4807 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d617, d58747, d4807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
    | true =>
      simp only [d617, d58747, d4807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d618 q = 1) (hb : d58747 q = 1) : d4808 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d618, d4808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d618, d4808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d619 q = 1) (hb : d58747 q = 1) : d4809 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d619, d4809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
    | true =>
      simp only [d619, d4809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h31 (q : Pattern) (ha : d1 q = 1) (hb : d620 q = 1) : d620 q = 1 := by
    exact hb
  have h32 (q : Pattern) (ha : d0 q = 1) (hb : d500 q = 1) : d0 q = 1 := by
    exact ha
  have h33 (q : Pattern) (ha : d621 q = 1) (hb : d58747 q = 1) : d4810 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d621, d58747, d4810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q hb ha
    | true =>
      simp only [d621, d58747, d4810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q hb ha
  have h34 (q : Pattern) (ha : d4413 q = 1) (hb : d58747 q = 1) : d69512 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4413, d69512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
    | true =>
      simp only [d4413, d69512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h35 (q : Pattern) (ha : d627 q = 1) (hb : d58747 q = 1) : d627 q = 1 := by
    exact ha
  have h36 (q : Pattern) (ha : d4414 q = 1) (hb : d58747 q = 1) : d69513 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4414, d69513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
    | true =>
      simp only [d4414, d69513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h35 q ha hb
  have h37 (q : Pattern) (ha : d51686 q = 1) (hb : d58747 q = 1) : d69514 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51686, d69514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
    | true =>
      simp only [d51686, d69514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h36 q ha hb
  have h38 (q : Pattern) (ha : d51687 q = 1) (hb : d58747 q = 1) : d69515 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51687, d69515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d51687, d69515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h37 q ha hb
  have h39 (q : Pattern) (ha : d51688 q = 1) (hb : d58747 q = 1) : d69516 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51688, d69516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d51688, d69516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h38 q ha hb
  exact h39 p ha hb
theorem andIntro4218 (p : Pattern) (ha : d58635 p = 1) (hb : d68751 p = 1) : d69539 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d498 q = 1) (hb : d58747 q = 1) : d4779 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d498, d4779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d498, d4779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4212 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d499 q = 1) (hb : d68751 q = 1) : d4780 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d499, d68751, d4780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d499, d68751, d4780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d508 q = 1) (hb : d58747 q = 1) : d4786 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, d4786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4212 q ha hb
    | true =>
      simp only [d508, d4786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4213 q ha hb
  have h5 (q : Pattern) (ha : d509 q = 1) (hb : d68751 q = 1) : d4787 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, d68751, d4787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d509, d68751, d4787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d510 q = 1) (hb : d68751 q = 1) : d4788 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d510, d4788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d510, d4788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51689 q = 1) (hb : d58747 q = 1) : d69517 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51689, d69517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4216 q ha hb
    | true =>
      simp only [d51689, d69517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4217 q ha hb
  have h8 (q : Pattern) (ha : d58631 q = 1) (hb : d68751 q = 1) : d69518 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58631, d68751, d69518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d58631, d68751, d69518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d68751 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d58632 q = 1) (hb : d68751 q = 1) : d69519 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58632, d69519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58632, d69519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d58633 q = 1) (hb : d68751 q = 1) : d69520 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58633, d69520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58633, d69520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4423 q = 1) (hb : d58747 q = 1) : d69524 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4423, d69524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4423, d69524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4214 q ha hb
  have h13 (q : Pattern) (ha : d4424 q = 1) (hb : d68751 q = 1) : d69525 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4424, d68751, d69525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4424, d68751, d69525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d4425 q = 1) (hb : d68751 q = 1) : d69526 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4425, d69526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4425, d69526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h15 (q : Pattern) (ha : d4426 q = 1) (hb : d68751 q = 1) : d69527 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4426, d69527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4426, d69527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h16 (q : Pattern) (ha : d58634 q = 1) (hb : d68751 q = 1) : d69528 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58634, d69528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d58634, d69528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d4433 q = 1) (hb : d58747 q = 1) : d69534 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4433, d69534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4433, d69534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4215 q ha hb
  have h18 (q : Pattern) (ha : d4434 q = 1) (hb : d68751 q = 1) : d69535 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4434, d68751, d69535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d4434, d68751, d69535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h19 (q : Pattern) (ha : d4435 q = 1) (hb : d68751 q = 1) : d69536 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4435, d69536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d4435, d69536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h20 (q : Pattern) (ha : d4436 q = 1) (hb : d68751 q = 1) : d69537 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4436, d69537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4436, d69537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h21 (q : Pattern) (ha : d4437 q = 1) (hb : d68751 q = 1) : d69538 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4437, d69538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d4437, d69538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h22 (q : Pattern) (ha : d58635 q = 1) (hb : d68751 q = 1) : d69539 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58635, d69539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d58635, d69539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro4219 (p : Pattern) (ha : d58641 p = 1) (hb : d68751 p = 1) : d69545 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68751 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58636 q = 1) (hb : d68751 q = 1) : d69540 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58636, d69540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58636, d69540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4218 q ha hb
  have h2 (q : Pattern) (ha : d58637 q = 1) (hb : d68751 q = 1) : d69541 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58637, d69541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58637, d69541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58638 q = 1) (hb : d68751 q = 1) : d69542 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58638, d69542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58638, d69542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58639 q = 1) (hb : d68751 q = 1) : d69543 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58639, d69543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58639, d69543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58640 q = 1) (hb : d68751 q = 1) : d69544 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58640, d69544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58640, d69544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58641 q = 1) (hb : d68751 q = 1) : d69545 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58641, d69545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58641, d69545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4220 (p : Pattern) (ha : d789 p = 1) (hb : d58747 p = 1) : d4873 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d779 q = 1) : d779 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d783 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d784 q = 1) (hb : d58747 q = 1) : d909 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d784, d58747, d909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d784, d58747, d909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d785 q = 1) (hb : d58747 q = 1) : d4869 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, d4869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d785, d4869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d786 q = 1) (hb : d58747 q = 1) : d4870 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, d4870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d786, d4870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d787 q = 1) (hb : d58747 q = 1) : d4871 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, d4871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d787, d4871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d788 q = 1) (hb : d58747 q = 1) : d4872 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, d4872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, d4872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d789 q = 1) (hb : d58747 q = 1) : d4873 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d789, d4873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d789, d4873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4221 (p : Pattern) (ha : d799 p = 1) (hb : d58747 p = 1) : d4880 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d779 q = 1) : d779 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d783 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d784 q = 1) (hb : d58747 q = 1) : d909 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d784, d58747, d909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d784, d58747, d909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d785 q = 1) (hb : d58747 q = 1) : d4869 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d785, d4869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d785, d4869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d786 q = 1) (hb : d58747 q = 1) : d4870 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d786, d4870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d786, d4870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d787 q = 1) (hb : d58747 q = 1) : d4871 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d787, d4871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d787, d4871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d788 q = 1) (hb : d58747 q = 1) : d4872 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d788, d4872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d788, d4872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d792 q = 1) : d792 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d793 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d794 q = 1) (hb : d58747 q = 1) : d932 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d794, d58747, d932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d794, d58747, d932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d795 q = 1) (hb : d58747 q = 1) : d4876 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d795, d4876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d795, d4876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d796 q = 1) (hb : d58747 q = 1) : d4877 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d796, d4877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d796, d4877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d797 q = 1) (hb : d58747 q = 1) : d4878 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d797, d4878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d797, d4878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d798 q = 1) (hb : d58747 q = 1) : d4879 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d798, d4879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d798, d4879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d799 q = 1) (hb : d58747 q = 1) : d4880 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d799, d4880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d799, d4880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro4222 (p : Pattern) (ha : d4460 p = 1) (hb : d58747 p = 1) : d69563 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d926 q = 1) : d926 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d792 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d927 q = 1) (hb : d58747 q = 1) : d4905 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d927, d58747, d4905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d927, d58747, d4905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4451 q = 1) (hb : d58747 q = 1) : d69552 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4451, d69552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4451, d69552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d933 q = 1) (hb : d58747 q = 1) : d933 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d4452 q = 1) (hb : d58747 q = 1) : d69553 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4452, d69553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4452, d69553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4453 q = 1) (hb : d58747 q = 1) : d69561 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4453, d69561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4453, d69561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4454 q = 1) (hb : d58747 q = 1) : d69562 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4454, d69562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4454, d69562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4460 q = 1) (hb : d58747 q = 1) : d69563 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4460, d69563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4460, d69563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro4223 (p : Pattern) (ha : d4470 p = 1) (hb : d58747 p = 1) : d69573 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1003 q = 1) : d1003 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1011 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1012 q = 1) (hb : d58747 q = 1) : d4944 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1012, d58747, d4944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1012, d58747, d4944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4466 q = 1) (hb : d58747 q = 1) : d69569 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4466, d69569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4466, d69569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1054 q = 1) (hb : d58747 q = 1) : d1054 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d4467 q = 1) (hb : d58747 q = 1) : d69570 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4467, d69570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4467, d69570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4468 q = 1) (hb : d58747 q = 1) : d69571 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4468, d69571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4468, d69571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4469 q = 1) (hb : d58747 q = 1) : d69572 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4469, d69572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4469, d69572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4470 q = 1) (hb : d58747 q = 1) : d69573 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4470, d69573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4470, d69573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro4224 (p : Pattern) (ha : d51711 p = 1) (hb : d58747 p = 1) : d69551 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d804 q = 1) : d804 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d806 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d807 q = 1) (hb : d58747 q = 1) : d4884 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d807, d58747, d4884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d807, d58747, d4884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d808 q = 1) (hb : d58747 q = 1) : d4885 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d808, d4885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d808, d4885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d809 q = 1) (hb : d58747 q = 1) : d4886 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d809, d4886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d809, d4886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d810 q = 1) (hb : d58747 q = 1) : d4887 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d810, d4887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d810, d4887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d813 q = 1) : d813 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d816 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d817 q = 1) (hb : d58747 q = 1) : d4888 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d817, d58747, d4888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d817, d58747, d4888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d818 q = 1) (hb : d58747 q = 1) : d4889 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d818, d4889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d818, d4889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d819 q = 1) (hb : d58747 q = 1) : d4890 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d819, d4890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d819, d4890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d1 q = 1) (hb : d851 q = 1) : d851 q = 1 := by
    exact hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d779 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d852 q = 1) (hb : d58747 q = 1) : d4891 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d852, d58747, d4891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d852, d58747, d4891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d4446 q = 1) (hb : d58747 q = 1) : d69547 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4446, d69547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4446, d69547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d910 q = 1) (hb : d58747 q = 1) : d910 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d4447 q = 1) (hb : d58747 q = 1) : d69548 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4447, d69548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4447, d69548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d51709 q = 1) (hb : d58747 q = 1) : d69549 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51709, d69549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51709, d69549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d51710 q = 1) (hb : d58747 q = 1) : d69550 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51710, d69550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51710, d69550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d51711 q = 1) (hb : d58747 q = 1) : d69551 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51711, d69551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51711, d69551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro4225 (p : Pattern) (ha : d51714 p = 1) (hb : d58747 p = 1) : d69556 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d804 q = 1) : d804 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d806 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d807 q = 1) (hb : d58747 q = 1) : d4884 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d807, d58747, d4884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d807, d58747, d4884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d808 q = 1) (hb : d58747 q = 1) : d4885 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d808, d4885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d808, d4885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d809 q = 1) (hb : d58747 q = 1) : d4886 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d809, d4886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d809, d4886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d810 q = 1) (hb : d58747 q = 1) : d4887 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d810, d4887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d810, d4887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d813 q = 1) : d813 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d816 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d817 q = 1) (hb : d58747 q = 1) : d4888 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d817, d58747, d4888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d817, d58747, d4888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d818 q = 1) (hb : d58747 q = 1) : d4889 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d818, d4889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d818, d4889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d819 q = 1) (hb : d58747 q = 1) : d4890 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d819, d4890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d819, d4890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d1 q = 1) (hb : d851 q = 1) : d851 q = 1 := by
    exact hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d779 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d852 q = 1) (hb : d58747 q = 1) : d4891 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d852, d58747, d4891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d852, d58747, d4891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d4446 q = 1) (hb : d58747 q = 1) : d69547 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4446, d69547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4446, d69547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d910 q = 1) (hb : d58747 q = 1) : d910 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d4447 q = 1) (hb : d58747 q = 1) : d69548 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4447, d69548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4447, d69548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d51709 q = 1) (hb : d58747 q = 1) : d69549 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51709, d69549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51709, d69549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d51710 q = 1) (hb : d58747 q = 1) : d69550 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51710, d69550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51710, d69550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d1 q = 1) (hb : d915 q = 1) : d915 q = 1 := by
    exact hb
  have h21 (q : Pattern) (ha : d0 q = 1) (hb : d916 q = 1) : d0 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d917 q = 1) (hb : d58747 q = 1) : d4898 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d917, d58747, d4898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
    | true =>
      simp only [d917, d58747, d4898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
  have h23 (q : Pattern) (ha : d918 q = 1) (hb : d58747 q = 1) : d4899 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d918, d4899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d918, d4899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d919 q = 1) (hb : d58747 q = 1) : d4900 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d919, d4900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d919, d4900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d920 q = 1) (hb : d58747 q = 1) : d4901 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d920, d4901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d920, d4901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d1 q = 1) (hb : d921 q = 1) : d921 q = 1 := by
    exact hb
  have h27 (q : Pattern) (ha : d0 q = 1) (hb : d922 q = 1) : d0 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d923 q = 1) (hb : d58747 q = 1) : d4902 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d923, d58747, d4902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
    | true =>
      simp only [d923, d58747, d4902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d924 q = 1) (hb : d58747 q = 1) : d4903 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d924, d4903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d924, d4903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d925 q = 1) (hb : d58747 q = 1) : d4904 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d925, d4904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
    | true =>
      simp only [d925, d4904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h31 (q : Pattern) (ha : d1 q = 1) (hb : d926 q = 1) : d926 q = 1 := by
    exact hb
  have h32 (q : Pattern) (ha : d0 q = 1) (hb : d792 q = 1) : d0 q = 1 := by
    exact ha
  have h33 (q : Pattern) (ha : d927 q = 1) (hb : d58747 q = 1) : d4905 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d927, d58747, d4905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q hb ha
    | true =>
      simp only [d927, d58747, d4905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q hb ha
  have h34 (q : Pattern) (ha : d4451 q = 1) (hb : d58747 q = 1) : d69552 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4451, d69552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
    | true =>
      simp only [d4451, d69552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h35 (q : Pattern) (ha : d933 q = 1) (hb : d58747 q = 1) : d933 q = 1 := by
    exact ha
  have h36 (q : Pattern) (ha : d4452 q = 1) (hb : d58747 q = 1) : d69553 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4452, d69553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
    | true =>
      simp only [d4452, d69553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h35 q ha hb
  have h37 (q : Pattern) (ha : d51712 q = 1) (hb : d58747 q = 1) : d69554 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51712, d69554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
    | true =>
      simp only [d51712, d69554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h36 q ha hb
  have h38 (q : Pattern) (ha : d51713 q = 1) (hb : d58747 q = 1) : d69555 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51713, d69555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d51713, d69555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h37 q ha hb
  have h39 (q : Pattern) (ha : d51714 q = 1) (hb : d58747 q = 1) : d69556 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51714, d69556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d51714, d69556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h38 q ha hb
  exact h39 p ha hb
theorem andIntro4226 (p : Pattern) (ha : d58647 p = 1) (hb : d68751 p = 1) : d69579 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d790 q = 1) (hb : d58747 q = 1) : d4874 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d790, d4874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d790, d4874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4220 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d791 q = 1) (hb : d68751 q = 1) : d4875 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d791, d68751, d4875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d791, d68751, d4875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d800 q = 1) (hb : d58747 q = 1) : d4881 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d4881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4220 q ha hb
    | true =>
      simp only [d800, d4881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4221 q ha hb
  have h5 (q : Pattern) (ha : d801 q = 1) (hb : d68751 q = 1) : d4882 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d68751, d4882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d801, d68751, d4882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d802 q = 1) (hb : d68751 q = 1) : d4883 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d802, d4883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d802, d4883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51715 q = 1) (hb : d58747 q = 1) : d69557 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51715, d69557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4224 q ha hb
    | true =>
      simp only [d51715, d69557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4225 q ha hb
  have h8 (q : Pattern) (ha : d58643 q = 1) (hb : d68751 q = 1) : d69558 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58643, d68751, d69558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d58643, d68751, d69558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d68751 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d58644 q = 1) (hb : d68751 q = 1) : d69559 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58644, d69559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58644, d69559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d58645 q = 1) (hb : d68751 q = 1) : d69560 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58645, d69560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58645, d69560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4461 q = 1) (hb : d58747 q = 1) : d69564 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4461, d69564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4461, d69564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4222 q ha hb
  have h13 (q : Pattern) (ha : d4462 q = 1) (hb : d68751 q = 1) : d69565 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4462, d68751, d69565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4462, d68751, d69565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d4463 q = 1) (hb : d68751 q = 1) : d69566 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4463, d69566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4463, d69566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h15 (q : Pattern) (ha : d4464 q = 1) (hb : d68751 q = 1) : d69567 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4464, d69567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4464, d69567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h16 (q : Pattern) (ha : d58646 q = 1) (hb : d68751 q = 1) : d69568 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58646, d69568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d58646, d69568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d4471 q = 1) (hb : d58747 q = 1) : d69574 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4471, d69574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4471, d69574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4223 q ha hb
  have h18 (q : Pattern) (ha : d4472 q = 1) (hb : d68751 q = 1) : d69575 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4472, d68751, d69575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d4472, d68751, d69575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h19 (q : Pattern) (ha : d4473 q = 1) (hb : d68751 q = 1) : d69576 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4473, d69576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d4473, d69576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h20 (q : Pattern) (ha : d4474 q = 1) (hb : d68751 q = 1) : d69577 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4474, d69577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4474, d69577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h21 (q : Pattern) (ha : d4475 q = 1) (hb : d68751 q = 1) : d69578 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4475, d69578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d4475, d69578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h22 (q : Pattern) (ha : d58647 q = 1) (hb : d68751 q = 1) : d69579 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58647, d69579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d58647, d69579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro4227 (p : Pattern) (ha : d58653 p = 1) (hb : d68751 p = 1) : d69585 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68751 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58648 q = 1) (hb : d68751 q = 1) : d69580 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58648, d69580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58648, d69580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4226 q ha hb
  have h2 (q : Pattern) (ha : d58649 q = 1) (hb : d68751 q = 1) : d69581 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58649, d69581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58649, d69581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58650 q = 1) (hb : d68751 q = 1) : d69582 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58650, d69582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58650, d69582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58651 q = 1) (hb : d68751 q = 1) : d69583 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58651, d69583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58651, d69583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58652 q = 1) (hb : d68751 q = 1) : d69584 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58652, d69584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58652, d69584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58653 q = 1) (hb : d68751 q = 1) : d69585 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58653, d69585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58653, d69585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4228 (p : Pattern) (ha : d1168 p = 1) (hb : d58747 p = 1) : d4969 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1158 q = 1) : d1158 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1162 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1163 q = 1) (hb : d58747 q = 1) : d1320 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1163, d58747, d1320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1163, d58747, d1320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1164 q = 1) (hb : d58747 q = 1) : d4965 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, d4965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1164, d4965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1165 q = 1) (hb : d58747 q = 1) : d4966 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d4966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1165, d4966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1166 q = 1) (hb : d58747 q = 1) : d4967 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, d4967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1166, d4967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1167 q = 1) (hb : d58747 q = 1) : d4968 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, d4968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, d4968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1168 q = 1) (hb : d58747 q = 1) : d4969 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1168, d4969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1168, d4969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4229 (p : Pattern) (ha : d1178 p = 1) (hb : d58747 p = 1) : d4976 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1158 q = 1) : d1158 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1162 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1163 q = 1) (hb : d58747 q = 1) : d1320 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1163, d58747, d1320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1163, d58747, d1320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1164 q = 1) (hb : d58747 q = 1) : d4965 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, d4965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1164, d4965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1165 q = 1) (hb : d58747 q = 1) : d4966 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d4966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1165, d4966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1166 q = 1) (hb : d58747 q = 1) : d4967 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, d4967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1166, d4967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1167 q = 1) (hb : d58747 q = 1) : d4968 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, d4968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, d4968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d1171 q = 1) : d1171 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1172 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1173 q = 1) (hb : d58747 q = 1) : d1343 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1173, d58747, d1343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d1173, d58747, d1343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d1174 q = 1) (hb : d58747 q = 1) : d4972 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1174, d4972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1174, d4972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1175 q = 1) (hb : d58747 q = 1) : d4973 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1175, d4973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1175, d4973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1176 q = 1) (hb : d58747 q = 1) : d4974 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1176, d4974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1176, d4974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1177 q = 1) (hb : d58747 q = 1) : d4975 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1177, d4975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1177, d4975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d1178 q = 1) (hb : d58747 q = 1) : d4976 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1178, d4976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1178, d4976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro4230 (p : Pattern) (ha : d4499 p = 1) (hb : d58747 p = 1) : d69604 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1337 q = 1) : d1337 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1171 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1338 q = 1) (hb : d58747 q = 1) : d5001 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1338, d58747, d5001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1338, d58747, d5001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4490 q = 1) (hb : d58747 q = 1) : d69593 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4490, d69593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4490, d69593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1344 q = 1) (hb : d58747 q = 1) : d1344 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d4491 q = 1) (hb : d58747 q = 1) : d69594 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4491, d69594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4491, d69594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4492 q = 1) (hb : d58747 q = 1) : d69602 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4492, d69602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4492, d69602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4493 q = 1) (hb : d58747 q = 1) : d69603 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4493, d69603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4493, d69603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4499 q = 1) (hb : d58747 q = 1) : d69604 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4499, d69604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4499, d69604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro4231 (p : Pattern) (ha : d4509 p = 1) (hb : d58747 p = 1) : d69614 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1428 q = 1) : d1428 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1436 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1437 q = 1) (hb : d58747 q = 1) : d5054 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1437, d58747, d5054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1437, d58747, d5054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4505 q = 1) (hb : d58747 q = 1) : d69610 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4505, d69610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4505, d69610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1488 q = 1) (hb : d58747 q = 1) : d1488 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d4506 q = 1) (hb : d58747 q = 1) : d69611 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4506, d69611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4506, d69611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4507 q = 1) (hb : d58747 q = 1) : d69612 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4507, d69612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4507, d69612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4508 q = 1) (hb : d58747 q = 1) : d69613 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4508, d69613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4508, d69613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4509 q = 1) (hb : d58747 q = 1) : d69614 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4509, d69614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4509, d69614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro4232 (p : Pattern) (ha : d51738 p = 1) (hb : d58747 p = 1) : d69592 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1183 q = 1) : d1183 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1185 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1186 q = 1) (hb : d58747 q = 1) : d4980 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1186, d58747, d4980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1186, d58747, d4980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1187 q = 1) (hb : d58747 q = 1) : d4981 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1187, d4981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1187, d4981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1188 q = 1) (hb : d58747 q = 1) : d4982 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, d4982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1188, d4982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1189 q = 1) (hb : d58747 q = 1) : d4983 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, d4983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1189, d4983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d1192 q = 1) : d1192 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1195 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1196 q = 1) (hb : d58747 q = 1) : d4984 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1196, d58747, d4984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d1196, d58747, d4984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d1197 q = 1) (hb : d58747 q = 1) : d4985 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1197, d4985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1197, d4985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1198 q = 1) (hb : d58747 q = 1) : d4986 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, d4986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1198, d4986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d1 q = 1) (hb : d1227 q = 1) : d1227 q = 1 := by
    exact hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d1158 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d1228 q = 1) (hb : d58747 q = 1) : d4987 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1228, d58747, d4987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d1228, d58747, d4987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d4485 q = 1) (hb : d58747 q = 1) : d69588 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4485, d69588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4485, d69588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d1321 q = 1) (hb : d58747 q = 1) : d1321 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d4486 q = 1) (hb : d58747 q = 1) : d69589 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4486, d69589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4486, d69589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d51736 q = 1) (hb : d58747 q = 1) : d69590 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51736, d69590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51736, d69590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d51737 q = 1) (hb : d58747 q = 1) : d69591 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51737, d69591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51737, d69591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d51738 q = 1) (hb : d58747 q = 1) : d69592 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51738, d69592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51738, d69592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro4233 (p : Pattern) (ha : d51741 p = 1) (hb : d58747 p = 1) : d69597 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1183 q = 1) : d1183 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1185 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1186 q = 1) (hb : d58747 q = 1) : d4980 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1186, d58747, d4980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1186, d58747, d4980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1187 q = 1) (hb : d58747 q = 1) : d4981 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1187, d4981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1187, d4981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1188 q = 1) (hb : d58747 q = 1) : d4982 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, d4982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1188, d4982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1189 q = 1) (hb : d58747 q = 1) : d4983 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, d4983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1189, d4983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d1192 q = 1) : d1192 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1195 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1196 q = 1) (hb : d58747 q = 1) : d4984 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1196, d58747, d4984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d1196, d58747, d4984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d1197 q = 1) (hb : d58747 q = 1) : d4985 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1197, d4985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1197, d4985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1198 q = 1) (hb : d58747 q = 1) : d4986 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, d4986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1198, d4986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d1 q = 1) (hb : d1227 q = 1) : d1227 q = 1 := by
    exact hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d1158 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d1228 q = 1) (hb : d58747 q = 1) : d4987 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1228, d58747, d4987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d1228, d58747, d4987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d4485 q = 1) (hb : d58747 q = 1) : d69588 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4485, d69588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4485, d69588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d1321 q = 1) (hb : d58747 q = 1) : d1321 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d4486 q = 1) (hb : d58747 q = 1) : d69589 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4486, d69589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4486, d69589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d51736 q = 1) (hb : d58747 q = 1) : d69590 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51736, d69590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51736, d69590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d51737 q = 1) (hb : d58747 q = 1) : d69591 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51737, d69591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51737, d69591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d1 q = 1) (hb : d1326 q = 1) : d1326 q = 1 := by
    exact hb
  have h21 (q : Pattern) (ha : d0 q = 1) (hb : d1327 q = 1) : d0 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d1328 q = 1) (hb : d58747 q = 1) : d4994 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1328, d58747, d4994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
    | true =>
      simp only [d1328, d58747, d4994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
  have h23 (q : Pattern) (ha : d1329 q = 1) (hb : d58747 q = 1) : d4995 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1329, d4995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1329, d4995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d1330 q = 1) (hb : d58747 q = 1) : d4996 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1330, d4996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d1330, d4996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d1331 q = 1) (hb : d58747 q = 1) : d4997 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1331, d4997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1331, d4997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d1 q = 1) (hb : d1332 q = 1) : d1332 q = 1 := by
    exact hb
  have h27 (q : Pattern) (ha : d0 q = 1) (hb : d1333 q = 1) : d0 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d1334 q = 1) (hb : d58747 q = 1) : d4998 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1334, d58747, d4998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
    | true =>
      simp only [d1334, d58747, d4998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d1335 q = 1) (hb : d58747 q = 1) : d4999 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1335, d4999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1335, d4999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d1336 q = 1) (hb : d58747 q = 1) : d5000 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1336, d5000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
    | true =>
      simp only [d1336, d5000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h31 (q : Pattern) (ha : d1 q = 1) (hb : d1337 q = 1) : d1337 q = 1 := by
    exact hb
  have h32 (q : Pattern) (ha : d0 q = 1) (hb : d1171 q = 1) : d0 q = 1 := by
    exact ha
  have h33 (q : Pattern) (ha : d1338 q = 1) (hb : d58747 q = 1) : d5001 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1338, d58747, d5001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q hb ha
    | true =>
      simp only [d1338, d58747, d5001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q hb ha
  have h34 (q : Pattern) (ha : d4490 q = 1) (hb : d58747 q = 1) : d69593 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4490, d69593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
    | true =>
      simp only [d4490, d69593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h35 (q : Pattern) (ha : d1344 q = 1) (hb : d58747 q = 1) : d1344 q = 1 := by
    exact ha
  have h36 (q : Pattern) (ha : d4491 q = 1) (hb : d58747 q = 1) : d69594 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4491, d69594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
    | true =>
      simp only [d4491, d69594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h35 q ha hb
  have h37 (q : Pattern) (ha : d51739 q = 1) (hb : d58747 q = 1) : d69595 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51739, d69595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
    | true =>
      simp only [d51739, d69595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h36 q ha hb
  have h38 (q : Pattern) (ha : d51740 q = 1) (hb : d58747 q = 1) : d69596 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51740, d69596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d51740, d69596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h37 q ha hb
  have h39 (q : Pattern) (ha : d51741 q = 1) (hb : d58747 q = 1) : d69597 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51741, d69597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d51741, d69597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h38 q ha hb
  exact h39 p ha hb
theorem andIntro4234 (p : Pattern) (ha : d58660 p = 1) (hb : d68751 p = 1) : d69620 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1169 q = 1) (hb : d58747 q = 1) : d4970 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1169, d4970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1169, d4970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4228 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1170 q = 1) (hb : d68751 q = 1) : d4971 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1170, d68751, d4971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1170, d68751, d4971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1179 q = 1) (hb : d58747 q = 1) : d4977 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d4977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4228 q ha hb
    | true =>
      simp only [d1179, d4977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4229 q ha hb
  have h5 (q : Pattern) (ha : d1180 q = 1) (hb : d68751 q = 1) : d4978 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d68751, d4978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1180, d68751, d4978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d1181 q = 1) (hb : d68751 q = 1) : d4979 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1181, d4979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1181, d4979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51742 q = 1) (hb : d58747 q = 1) : d69598 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51742, d69598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4232 q ha hb
    | true =>
      simp only [d51742, d69598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4233 q ha hb
  have h8 (q : Pattern) (ha : d58656 q = 1) (hb : d68751 q = 1) : d69599 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58656, d68751, d69599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d58656, d68751, d69599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d68751 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d58657 q = 1) (hb : d68751 q = 1) : d69600 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58657, d69600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58657, d69600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d58658 q = 1) (hb : d68751 q = 1) : d69601 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58658, d69601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58658, d69601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4500 q = 1) (hb : d58747 q = 1) : d69605 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4500, d69605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4500, d69605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4230 q ha hb
  have h13 (q : Pattern) (ha : d4501 q = 1) (hb : d68751 q = 1) : d69606 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4501, d68751, d69606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4501, d68751, d69606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d4502 q = 1) (hb : d68751 q = 1) : d69607 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4502, d69607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4502, d69607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h15 (q : Pattern) (ha : d4503 q = 1) (hb : d68751 q = 1) : d69608 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4503, d69608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4503, d69608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h16 (q : Pattern) (ha : d58659 q = 1) (hb : d68751 q = 1) : d69609 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58659, d69609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d58659, d69609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d4510 q = 1) (hb : d58747 q = 1) : d69615 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4510, d69615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4510, d69615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4231 q ha hb
  have h18 (q : Pattern) (ha : d4511 q = 1) (hb : d68751 q = 1) : d69616 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4511, d68751, d69616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d4511, d68751, d69616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h19 (q : Pattern) (ha : d4512 q = 1) (hb : d68751 q = 1) : d69617 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4512, d69617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d4512, d69617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h20 (q : Pattern) (ha : d4513 q = 1) (hb : d68751 q = 1) : d69618 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4513, d69618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4513, d69618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h21 (q : Pattern) (ha : d4514 q = 1) (hb : d68751 q = 1) : d69619 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4514, d69619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d4514, d69619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h22 (q : Pattern) (ha : d58660 q = 1) (hb : d68751 q = 1) : d69620 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58660, d69620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d58660, d69620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro4235 (p : Pattern) (ha : d58666 p = 1) (hb : d68751 p = 1) : d69626 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68751 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58661 q = 1) (hb : d68751 q = 1) : d69621 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58661, d69621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58661, d69621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4234 q ha hb
  have h2 (q : Pattern) (ha : d58662 q = 1) (hb : d68751 q = 1) : d69622 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58662, d69622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58662, d69622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58663 q = 1) (hb : d68751 q = 1) : d69623 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58663, d69623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58663, d69623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58664 q = 1) (hb : d68751 q = 1) : d69624 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58664, d69624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58664, d69624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58665 q = 1) (hb : d68751 q = 1) : d69625 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58665, d69625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58665, d69625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58666 q = 1) (hb : d68751 q = 1) : d69626 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58666, d69626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58666, d69626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4236 (p : Pattern) (ha : d1629 p = 1) (hb : d58747 p = 1) : d5080 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1619 q = 1) : d1619 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1623 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1624 q = 1) (hb : d58747 q = 1) : d1797 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1624, d58747, d1797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1624, d58747, d1797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1625 q = 1) (hb : d58747 q = 1) : d5076 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d5076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1625, d5076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1626 q = 1) (hb : d58747 q = 1) : d5077 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d5077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1626, d5077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1627 q = 1) (hb : d58747 q = 1) : d5078 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, d5078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1627, d5078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1628 q = 1) (hb : d58747 q = 1) : d5079 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, d5079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, d5079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1629 q = 1) (hb : d58747 q = 1) : d5080 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1629, d5080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1629, d5080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4237 (p : Pattern) (ha : d1639 p = 1) (hb : d58747 p = 1) : d5087 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1619 q = 1) : d1619 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1623 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1624 q = 1) (hb : d58747 q = 1) : d1797 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1624, d58747, d1797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1624, d58747, d1797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1625 q = 1) (hb : d58747 q = 1) : d5076 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d5076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1625, d5076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1626 q = 1) (hb : d58747 q = 1) : d5077 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d5077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1626, d5077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1627 q = 1) (hb : d58747 q = 1) : d5078 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, d5078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1627, d5078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1628 q = 1) (hb : d58747 q = 1) : d5079 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, d5079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, d5079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d1632 q = 1) : d1632 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1633 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1634 q = 1) (hb : d58747 q = 1) : d1820 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1634, d58747, d1820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d1634, d58747, d1820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d1635 q = 1) (hb : d58747 q = 1) : d5083 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1635, d5083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1635, d5083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1636 q = 1) (hb : d58747 q = 1) : d5084 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1636, d5084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1636, d5084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1637 q = 1) (hb : d58747 q = 1) : d5085 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1637, d5085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1637, d5085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1638 q = 1) (hb : d58747 q = 1) : d5086 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1638, d5086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1638, d5086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d1639 q = 1) (hb : d58747 q = 1) : d5087 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1639, d5087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1639, d5087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro4238 (p : Pattern) (ha : d4539 p = 1) (hb : d58747 p = 1) : d69646 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1814 q = 1) : d1814 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1632 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1815 q = 1) (hb : d58747 q = 1) : d5112 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1815, d58747, d5112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1815, d58747, d5112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4530 q = 1) (hb : d58747 q = 1) : d69635 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4530, d69635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4530, d69635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1821 q = 1) (hb : d58747 q = 1) : d1821 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d4531 q = 1) (hb : d58747 q = 1) : d69636 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4531, d69636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4531, d69636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4532 q = 1) (hb : d58747 q = 1) : d69644 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4532, d69644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4532, d69644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4533 q = 1) (hb : d58747 q = 1) : d69645 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4533, d69645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4533, d69645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4539 q = 1) (hb : d58747 q = 1) : d69646 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4539, d69646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4539, d69646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro4239 (p : Pattern) (ha : d4549 p = 1) (hb : d58747 p = 1) : d69656 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1905 q = 1) : d1905 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1913 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1914 q = 1) (hb : d58747 q = 1) : d5170 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1914, d58747, d5170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1914, d58747, d5170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4545 q = 1) (hb : d58747 q = 1) : d69652 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4545, d69652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4545, d69652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1965 q = 1) (hb : d58747 q = 1) : d1965 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d4546 q = 1) (hb : d58747 q = 1) : d69653 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4546, d69653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4546, d69653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4547 q = 1) (hb : d58747 q = 1) : d69654 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4547, d69654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4547, d69654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4548 q = 1) (hb : d58747 q = 1) : d69655 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4548, d69655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4548, d69655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4549 q = 1) (hb : d58747 q = 1) : d69656 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4549, d69656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4549, d69656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro4240 (p : Pattern) (ha : d51766 p = 1) (hb : d58747 p = 1) : d69634 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1644 q = 1) : d1644 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1646 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1647 q = 1) (hb : d58747 q = 1) : d5091 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1647, d58747, d5091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1647, d58747, d5091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1648 q = 1) (hb : d58747 q = 1) : d5092 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1648, d5092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1648, d5092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1649 q = 1) (hb : d58747 q = 1) : d5093 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, d5093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1649, d5093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1650 q = 1) (hb : d58747 q = 1) : d5094 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, d5094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1650, d5094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d1653 q = 1) : d1653 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1656 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1657 q = 1) (hb : d58747 q = 1) : d5095 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1657, d58747, d5095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d1657, d58747, d5095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d1658 q = 1) (hb : d58747 q = 1) : d5096 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1658, d5096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1658, d5096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1659 q = 1) (hb : d58747 q = 1) : d5097 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, d5097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1659, d5097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d1 q = 1) (hb : d1682 q = 1) : d1682 q = 1 := by
    exact hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d1619 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d1683 q = 1) (hb : d58747 q = 1) : d5098 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1683, d58747, d5098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d1683, d58747, d5098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d4525 q = 1) (hb : d58747 q = 1) : d69630 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4525, d69630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4525, d69630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d1798 q = 1) (hb : d58747 q = 1) : d1798 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d4526 q = 1) (hb : d58747 q = 1) : d69631 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4526, d69631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4526, d69631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d51764 q = 1) (hb : d58747 q = 1) : d69632 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51764, d69632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51764, d69632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d51765 q = 1) (hb : d58747 q = 1) : d69633 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51765, d69633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51765, d69633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d51766 q = 1) (hb : d58747 q = 1) : d69634 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51766, d69634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51766, d69634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro4241 (p : Pattern) (ha : d51769 p = 1) (hb : d58747 p = 1) : d69639 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1644 q = 1) : d1644 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1646 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1647 q = 1) (hb : d58747 q = 1) : d5091 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1647, d58747, d5091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1647, d58747, d5091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1648 q = 1) (hb : d58747 q = 1) : d5092 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1648, d5092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1648, d5092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1649 q = 1) (hb : d58747 q = 1) : d5093 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, d5093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1649, d5093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1650 q = 1) (hb : d58747 q = 1) : d5094 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, d5094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1650, d5094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d1653 q = 1) : d1653 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1656 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1657 q = 1) (hb : d58747 q = 1) : d5095 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1657, d58747, d5095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d1657, d58747, d5095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d1658 q = 1) (hb : d58747 q = 1) : d5096 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1658, d5096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1658, d5096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1659 q = 1) (hb : d58747 q = 1) : d5097 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, d5097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1659, d5097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d1 q = 1) (hb : d1682 q = 1) : d1682 q = 1 := by
    exact hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d1619 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d1683 q = 1) (hb : d58747 q = 1) : d5098 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1683, d58747, d5098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d1683, d58747, d5098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d4525 q = 1) (hb : d58747 q = 1) : d69630 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4525, d69630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4525, d69630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d1798 q = 1) (hb : d58747 q = 1) : d1798 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d4526 q = 1) (hb : d58747 q = 1) : d69631 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4526, d69631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4526, d69631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d51764 q = 1) (hb : d58747 q = 1) : d69632 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51764, d69632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51764, d69632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d51765 q = 1) (hb : d58747 q = 1) : d69633 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51765, d69633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51765, d69633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d1 q = 1) (hb : d1803 q = 1) : d1803 q = 1 := by
    exact hb
  have h21 (q : Pattern) (ha : d0 q = 1) (hb : d1804 q = 1) : d0 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d1805 q = 1) (hb : d58747 q = 1) : d5105 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1805, d58747, d5105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
    | true =>
      simp only [d1805, d58747, d5105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
  have h23 (q : Pattern) (ha : d1806 q = 1) (hb : d58747 q = 1) : d5106 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1806, d5106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1806, d5106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d1807 q = 1) (hb : d58747 q = 1) : d5107 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1807, d5107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d1807, d5107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d1808 q = 1) (hb : d58747 q = 1) : d5108 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1808, d5108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1808, d5108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d1 q = 1) (hb : d1809 q = 1) : d1809 q = 1 := by
    exact hb
  have h27 (q : Pattern) (ha : d0 q = 1) (hb : d1810 q = 1) : d0 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d1811 q = 1) (hb : d58747 q = 1) : d5109 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1811, d58747, d5109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
    | true =>
      simp only [d1811, d58747, d5109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d1812 q = 1) (hb : d58747 q = 1) : d5110 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1812, d5110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1812, d5110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d1813 q = 1) (hb : d58747 q = 1) : d5111 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1813, d5111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
    | true =>
      simp only [d1813, d5111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h31 (q : Pattern) (ha : d1 q = 1) (hb : d1814 q = 1) : d1814 q = 1 := by
    exact hb
  have h32 (q : Pattern) (ha : d0 q = 1) (hb : d1632 q = 1) : d0 q = 1 := by
    exact ha
  have h33 (q : Pattern) (ha : d1815 q = 1) (hb : d58747 q = 1) : d5112 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1815, d58747, d5112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q hb ha
    | true =>
      simp only [d1815, d58747, d5112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q hb ha
  have h34 (q : Pattern) (ha : d4530 q = 1) (hb : d58747 q = 1) : d69635 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4530, d69635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
    | true =>
      simp only [d4530, d69635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h35 (q : Pattern) (ha : d1821 q = 1) (hb : d58747 q = 1) : d1821 q = 1 := by
    exact ha
  have h36 (q : Pattern) (ha : d4531 q = 1) (hb : d58747 q = 1) : d69636 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4531, d69636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
    | true =>
      simp only [d4531, d69636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h35 q ha hb
  have h37 (q : Pattern) (ha : d51767 q = 1) (hb : d58747 q = 1) : d69637 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51767, d69637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
    | true =>
      simp only [d51767, d69637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h36 q ha hb
  have h38 (q : Pattern) (ha : d51768 q = 1) (hb : d58747 q = 1) : d69638 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51768, d69638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d51768, d69638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h37 q ha hb
  have h39 (q : Pattern) (ha : d51769 q = 1) (hb : d58747 q = 1) : d69639 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51769, d69639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d51769, d69639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h38 q ha hb
  exact h39 p ha hb
theorem andIntro4242 (p : Pattern) (ha : d58674 p = 1) (hb : d68751 p = 1) : d69662 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1630 q = 1) (hb : d58747 q = 1) : d5081 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1630, d5081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1630, d5081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4236 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1631 q = 1) (hb : d68751 q = 1) : d5082 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1631, d68751, d5082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1631, d68751, d5082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1640 q = 1) (hb : d58747 q = 1) : d5088 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d5088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4236 q ha hb
    | true =>
      simp only [d1640, d5088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4237 q ha hb
  have h5 (q : Pattern) (ha : d1641 q = 1) (hb : d68751 q = 1) : d5089 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d68751, d5089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1641, d68751, d5089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d1642 q = 1) (hb : d68751 q = 1) : d5090 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1642, d5090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1642, d5090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d51770 q = 1) (hb : d58747 q = 1) : d69640 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51770, d69640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4240 q ha hb
    | true =>
      simp only [d51770, d69640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4241 q ha hb
  have h8 (q : Pattern) (ha : d58670 q = 1) (hb : d68751 q = 1) : d69641 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d58670, d68751, d69641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d58670, d68751, d69641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d68751 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d58671 q = 1) (hb : d68751 q = 1) : d69642 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58671, d69642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d58671, d69642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d58672 q = 1) (hb : d68751 q = 1) : d69643 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58672, d69643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d58672, d69643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4540 q = 1) (hb : d58747 q = 1) : d69647 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4540, d69647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4540, d69647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4238 q ha hb
  have h13 (q : Pattern) (ha : d4541 q = 1) (hb : d68751 q = 1) : d69648 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4541, d68751, d69648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4541, d68751, d69648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d4542 q = 1) (hb : d68751 q = 1) : d69649 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4542, d69649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4542, d69649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h15 (q : Pattern) (ha : d4543 q = 1) (hb : d68751 q = 1) : d69650 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4543, d69650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4543, d69650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h16 (q : Pattern) (ha : d58673 q = 1) (hb : d68751 q = 1) : d69651 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58673, d69651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d58673, d69651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d4550 q = 1) (hb : d58747 q = 1) : d69657 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4550, d69657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4550, d69657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4239 q ha hb
  have h18 (q : Pattern) (ha : d4551 q = 1) (hb : d68751 q = 1) : d69658 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4551, d68751, d69658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d4551, d68751, d69658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h19 (q : Pattern) (ha : d4552 q = 1) (hb : d68751 q = 1) : d69659 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4552, d69659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d4552, d69659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h20 (q : Pattern) (ha : d4553 q = 1) (hb : d68751 q = 1) : d69660 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4553, d69660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d4553, d69660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h21 (q : Pattern) (ha : d4554 q = 1) (hb : d68751 q = 1) : d69661 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4554, d69661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d4554, d69661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h22 (q : Pattern) (ha : d58674 q = 1) (hb : d68751 q = 1) : d69662 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58674, d69662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d58674, d69662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro4243 (p : Pattern) (ha : d58680 p = 1) (hb : d68751 p = 1) : d69668 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68751 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d58675 q = 1) (hb : d68751 q = 1) : d69663 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58675, d69663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58675, d69663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4242 q ha hb
  have h2 (q : Pattern) (ha : d58676 q = 1) (hb : d68751 q = 1) : d69664 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58676, d69664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58676, d69664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d58677 q = 1) (hb : d68751 q = 1) : d69665 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58677, d69665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58677, d69665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d58678 q = 1) (hb : d68751 q = 1) : d69666 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58678, d69666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58678, d69666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d58679 q = 1) (hb : d68751 q = 1) : d69667 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58679, d69667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58679, d69667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d58680 q = 1) (hb : d68751 q = 1) : d69668 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58680, d69668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d58680, d69668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro4244 (p : Pattern) (ha : d2112 p = 1) (hb : d58747 p = 1) : d5197 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d2102 q = 1) : d2102 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2106 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2107 q = 1) (hb : d58747 q = 1) : d2275 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2107, d58747, d2275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2107, d58747, d2275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2108 q = 1) (hb : d58747 q = 1) : d5193 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d5193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2108, d5193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2109 q = 1) (hb : d58747 q = 1) : d5194 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d5194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2109, d5194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2110 q = 1) (hb : d58747 q = 1) : d5195 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, d5195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2110, d5195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2111 q = 1) (hb : d58747 q = 1) : d5196 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, d5196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, d5196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2112 q = 1) (hb : d58747 q = 1) : d5197 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2112, d5197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2112, d5197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro4245 (p : Pattern) (ha : d2122 p = 1) (hb : d58747 p = 1) : d5204 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d2102 q = 1) : d2102 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2106 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2107 q = 1) (hb : d58747 q = 1) : d2275 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2107, d58747, d2275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2107, d58747, d2275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2108 q = 1) (hb : d58747 q = 1) : d5193 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d5193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2108, d5193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2109 q = 1) (hb : d58747 q = 1) : d5194 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d5194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2109, d5194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2110 q = 1) (hb : d58747 q = 1) : d5195 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, d5195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2110, d5195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2111 q = 1) (hb : d58747 q = 1) : d5196 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, d5196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, d5196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1 q = 1) (hb : d2115 q = 1) : d2115 q = 1 := by
    exact hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d2116 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d2117 q = 1) (hb : d58747 q = 1) : d2298 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2117, d58747, d2298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d2117, d58747, d2298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d2118 q = 1) (hb : d58747 q = 1) : d5200 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2118, d5200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2118, d5200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2119 q = 1) (hb : d58747 q = 1) : d5201 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2119, d5201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2119, d5201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d2120 q = 1) (hb : d58747 q = 1) : d5202 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2120, d5202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2120, d5202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d2121 q = 1) (hb : d58747 q = 1) : d5203 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2121, d5203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2121, d5203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d2122 q = 1) (hb : d58747 q = 1) : d5204 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2122, d5204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2122, d5204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro4246 (p : Pattern) (ha : d4580 p = 1) (hb : d58747 p = 1) : d69689 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d2292 q = 1) : d2292 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2115 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2293 q = 1) (hb : d58747 q = 1) : d5229 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2293, d58747, d5229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2293, d58747, d5229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4571 q = 1) (hb : d58747 q = 1) : d69678 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4571, d69678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4571, d69678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2299 q = 1) (hb : d58747 q = 1) : d2299 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d4572 q = 1) (hb : d58747 q = 1) : d69679 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4572, d69679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4572, d69679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4573 q = 1) (hb : d58747 q = 1) : d69687 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4573, d69687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4573, d69687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4574 q = 1) (hb : d58747 q = 1) : d69688 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4574, d69688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4574, d69688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4580 q = 1) (hb : d58747 q = 1) : d69689 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4580, d69689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4580, d69689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro4247 (p : Pattern) (ha : d4590 p = 1) (hb : d58747 p = 1) : d69699 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d2383 q = 1) : d2383 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2391 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2392 q = 1) (hb : d58747 q = 1) : d5283 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2392, d58747, d5283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2392, d58747, d5283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d4586 q = 1) (hb : d58747 q = 1) : d69695 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4586, d69695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4586, d69695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2443 q = 1) (hb : d58747 q = 1) : d2443 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d4587 q = 1) (hb : d58747 q = 1) : d69696 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4587, d69696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4587, d69696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4588 q = 1) (hb : d58747 q = 1) : d69697 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4588, d69697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4588, d69697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4589 q = 1) (hb : d58747 q = 1) : d69698 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4589, d69698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4589, d69698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d4590 q = 1) (hb : d58747 q = 1) : d69699 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4590, d69699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4590, d69699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro4248 (p : Pattern) (ha : d51795 p = 1) (hb : d58747 p = 1) : d69677 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d2127 q = 1) : d2127 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2129 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2130 q = 1) (hb : d58747 q = 1) : d5208 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2130, d58747, d5208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2130, d58747, d5208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2131 q = 1) (hb : d58747 q = 1) : d5209 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2131, d5209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2131, d5209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2132 q = 1) (hb : d58747 q = 1) : d5210 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, d5210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2132, d5210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2133 q = 1) (hb : d58747 q = 1) : d5211 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, d5211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2133, d5211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d2136 q = 1) : d2136 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d2139 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d2140 q = 1) (hb : d58747 q = 1) : d5212 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2140, d58747, d5212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d2140, d58747, d5212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d2141 q = 1) (hb : d58747 q = 1) : d5213 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2141, d5213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2141, d5213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2142 q = 1) (hb : d58747 q = 1) : d5214 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, d5214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2142, d5214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d1 q = 1) (hb : d2161 q = 1) : d2161 q = 1 := by
    exact hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d2102 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d2162 q = 1) (hb : d58747 q = 1) : d5215 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2162, d58747, d5215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d2162, d58747, d5215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d4566 q = 1) (hb : d58747 q = 1) : d69673 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4566, d69673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4566, d69673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d2276 q = 1) (hb : d58747 q = 1) : d2276 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d4567 q = 1) (hb : d58747 q = 1) : d69674 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4567, d69674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4567, d69674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d51793 q = 1) (hb : d58747 q = 1) : d69675 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51793, d69675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51793, d69675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d51794 q = 1) (hb : d58747 q = 1) : d69676 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51794, d69676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51794, d69676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d51795 q = 1) (hb : d58747 q = 1) : d69677 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51795, d69677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51795, d69677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro4249 (p : Pattern) (ha : d51798 p = 1) (hb : d58747 p = 1) : d69682 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d58747 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d2127 q = 1) : d2127 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2129 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2130 q = 1) (hb : d58747 q = 1) : d5208 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2130, d58747, d5208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2130, d58747, d5208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2131 q = 1) (hb : d58747 q = 1) : d5209 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2131, d5209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2131, d5209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2132 q = 1) (hb : d58747 q = 1) : d5210 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, d5210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2132, d5210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2133 q = 1) (hb : d58747 q = 1) : d5211 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, d5211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2133, d5211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1 q = 1) (hb : d2136 q = 1) : d2136 q = 1 := by
    exact hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d2139 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d2140 q = 1) (hb : d58747 q = 1) : d5212 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2140, d58747, d5212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d2140, d58747, d5212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d2141 q = 1) (hb : d58747 q = 1) : d5213 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2141, d5213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2141, d5213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2142 q = 1) (hb : d58747 q = 1) : d5214 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, d5214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2142, d5214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d1 q = 1) (hb : d2161 q = 1) : d2161 q = 1 := by
    exact hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d2102 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d2162 q = 1) (hb : d58747 q = 1) : d5215 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2162, d58747, d5215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d2162, d58747, d5215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d4566 q = 1) (hb : d58747 q = 1) : d69673 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4566, d69673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4566, d69673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d2276 q = 1) (hb : d58747 q = 1) : d2276 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d4567 q = 1) (hb : d58747 q = 1) : d69674 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4567, d69674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4567, d69674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d51793 q = 1) (hb : d58747 q = 1) : d69675 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51793, d69675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51793, d69675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d51794 q = 1) (hb : d58747 q = 1) : d69676 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51794, d69676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51794, d69676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d1 q = 1) (hb : d2281 q = 1) : d2281 q = 1 := by
    exact hb
  have h21 (q : Pattern) (ha : d0 q = 1) (hb : d2282 q = 1) : d0 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d2283 q = 1) (hb : d58747 q = 1) : d5222 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2283, d58747, d5222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
    | true =>
      simp only [d2283, d58747, d5222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
  have h23 (q : Pattern) (ha : d2284 q = 1) (hb : d58747 q = 1) : d5223 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2284, d5223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2284, d5223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d2285 q = 1) (hb : d58747 q = 1) : d5224 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2285, d5224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d2285, d5224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d2286 q = 1) (hb : d58747 q = 1) : d5225 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2286, d5225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2286, d5225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d1 q = 1) (hb : d2287 q = 1) : d2287 q = 1 := by
    exact hb
  have h27 (q : Pattern) (ha : d0 q = 1) (hb : d2288 q = 1) : d0 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d2289 q = 1) (hb : d58747 q = 1) : d5226 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2289, d58747, d5226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
    | true =>
      simp only [d2289, d58747, d5226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d2290 q = 1) (hb : d58747 q = 1) : d5227 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2290, d5227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2290, d5227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d2291 q = 1) (hb : d58747 q = 1) : d5228 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2291, d5228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
    | true =>
      simp only [d2291, d5228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h31 (q : Pattern) (ha : d1 q = 1) (hb : d2292 q = 1) : d2292 q = 1 := by
    exact hb
  have h32 (q : Pattern) (ha : d0 q = 1) (hb : d2115 q = 1) : d0 q = 1 := by
    exact ha
  have h33 (q : Pattern) (ha : d2293 q = 1) (hb : d58747 q = 1) : d5229 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2293, d58747, d5229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q hb ha
    | true =>
      simp only [d2293, d58747, d5229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q hb ha
  have h34 (q : Pattern) (ha : d4571 q = 1) (hb : d58747 q = 1) : d69678 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4571, d69678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
    | true =>
      simp only [d4571, d69678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h35 (q : Pattern) (ha : d2299 q = 1) (hb : d58747 q = 1) : d2299 q = 1 := by
    exact ha
  have h36 (q : Pattern) (ha : d4572 q = 1) (hb : d58747 q = 1) : d69679 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4572, d69679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
    | true =>
      simp only [d4572, d69679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h35 q ha hb
  have h37 (q : Pattern) (ha : d51796 q = 1) (hb : d58747 q = 1) : d69680 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51796, d69680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
    | true =>
      simp only [d51796, d69680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h36 q ha hb
  have h38 (q : Pattern) (ha : d51797 q = 1) (hb : d58747 q = 1) : d69681 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51797, d69681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d51797, d69681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h37 q ha hb
  have h39 (q : Pattern) (ha : d51798 q = 1) (hb : d58747 q = 1) : d69682 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51798, d69682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d51798, d69682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h38 q ha hb
  exact h39 p ha hb
end NetHack.Soko22Hazard87
