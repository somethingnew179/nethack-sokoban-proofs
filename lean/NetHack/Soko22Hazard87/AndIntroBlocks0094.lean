import NetHack.Soko22Hazard87.AndIntroBlocks0093
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro23500 (p : Pattern) (ha : d101942 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101937 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23499 q ha hb
  have h2 (q : Pattern) (ha : d101938 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101939 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101940 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101941 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101942 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23501 (p : Pattern) (ha : d9833 p = 1) (hb : d102051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1109 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1110 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1110, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9826 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1111 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9827 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9828 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d1120 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d1121 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d1121, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d9829 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1122 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d9830 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9831 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d9832 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d9799 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d9800 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d9800, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d9801 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d9802 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d9803 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d9803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d9804 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d9804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d9820 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d9820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d9833 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro23502 (p : Pattern) (ha : d9869 p = 1) (hb : d102051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1120 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1121 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1121, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9829 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1122 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9830 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9831 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9868 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d9843 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d9844 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d9844, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d9845 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9846 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d9847 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9848 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9849 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d9869 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro23503 (p : Pattern) (ha : d9875 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9870 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23501 q ha hb
    | true =>
      simp only [d9870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23502 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9871 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9871, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9871, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9872 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9873 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9874 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9875 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23504 (p : Pattern) (ha : d10010 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9876 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23503 q ha hb
    | true =>
      simp only [d9876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9877 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10007 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10008 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10009 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10010 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23505 (p : Pattern) (ha : d10016 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10011 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23504 q ha hb
    | true =>
      simp only [d10011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10012 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10013 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10014 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10015 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10016 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23506 (p : Pattern) (ha : d9784 p = 1) (hb : d102051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1209 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1210 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1210, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1210, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9746 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1211 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9747 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9748 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d9752 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d9753 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9753, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d9753, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d9754 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9755 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d9756 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9757 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d9758 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d9762 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d9763 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9763, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d9763, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d9764 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d9765 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d9766 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d9766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d9767 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d9767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d0 q = 1) (hb : d9777 q = 1) : d0 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d9778 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9778, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d9778, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h23 (q : Pattern) (ha : d9779 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d9780 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d9780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d9781 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d9781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d9782 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d9782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d9783 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d9783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d9784 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  exact h28 p ha hb
theorem andIntro23507 (p : Pattern) (ha : d9806 p = 1) (hb : d102051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1099 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1100 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1100, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9785 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1101 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9786 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9787 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d9788 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d9789 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9789, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d9789, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d9790 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9791 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d9792 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9793 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d9794 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d9777 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d9778 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9778, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d9778, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d9779 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d9780 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d9781 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d9781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d9782 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d9782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d0 q = 1) (hb : d9799 q = 1) : d0 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d9800 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d9800, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h23 (q : Pattern) (ha : d9801 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d9802 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d9802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d9803 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d9803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d9804 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d9804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d9805 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d9805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d9806 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  exact h28 p ha hb
theorem andIntro23508 (p : Pattern) (ha : d9821 p = 1) (hb : d102051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9813 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9814 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9814, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d9814, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9815 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9816 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9817 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9818 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d9799 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d9800 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d9800, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d9801 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9802 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d9803 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9804 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d9819 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d9820 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d9821 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro23509 (p : Pattern) (ha : d9850 p = 1) (hb : d102051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5017 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5018 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5018, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d5018, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9837 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5019 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9838 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9839 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9840 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d9843 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d9844 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d9844, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d9845 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9846 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d9847 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9848 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9849 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d9850 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro23510 (p : Pattern) (ha : d9856 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9807 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23506 q ha hb
    | true =>
      simp only [d9807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23507 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9808 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9808, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9808, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9809 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9822 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23507 q ha hb
    | true =>
      simp only [d9822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23508 q ha hb
  have h6 (q : Pattern) (ha : d9823 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9823, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9823, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d9824 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9825 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9834 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23507 q ha hb
    | true =>
      simp only [d9834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23501 q ha hb
  have h10 (q : Pattern) (ha : d9835 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9835, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9835, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d9836 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9851 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23501 q ha hb
    | true =>
      simp only [d9851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23509 q ha hb
  have h13 (q : Pattern) (ha : d9852 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9852, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9852, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d9853 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d9854 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9855 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9856 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro23511 (p : Pattern) (ha : d9861 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9834 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23507 q ha hb
    | true =>
      simp only [d9834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23501 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9835 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9835, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9835, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9836 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9851 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23501 q ha hb
    | true =>
      simp only [d9851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23509 q ha hb
  have h6 (q : Pattern) (ha : d9852 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9852, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9852, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d9853 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9854 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9859 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d9860 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9861 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro23512 (p : Pattern) (ha : d9867 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9857 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23510 q ha hb
    | true =>
      simp only [d9857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9858 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9862 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23511 q ha hb
    | true =>
      simp only [d9862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9863 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9864 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9865 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9866 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9867 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23513 (p : Pattern) (ha : d9881 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9862 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23511 q ha hb
    | true =>
      simp only [d9862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9863 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9876 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23503 q ha hb
    | true =>
      simp only [d9876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9877 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9878 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9879 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9880 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9881 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23514 (p : Pattern) (ha : d9987 p = 1) (hb : d102051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1120 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1121 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1121, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9829 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1122 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9830 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d9830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9831 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d9831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9868 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d9868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d9987 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d9987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro23515 (p : Pattern) (ha : d9993 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9834 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23507 q ha hb
    | true =>
      simp only [d9834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23501 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9835 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9835, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9835, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9836 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9851 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23501 q ha hb
    | true =>
      simp only [d9851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23509 q ha hb
  have h6 (q : Pattern) (ha : d9852 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9852, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9852, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d9853 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9854 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9988 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23501 q ha hb
    | true =>
      simp only [d9988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23514 q ha hb
  have h10 (q : Pattern) (ha : d9989 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9989, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9989, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d9990 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9991 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d9992 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9993 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro23516 (p : Pattern) (ha : d9999 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9994 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23515 q ha hb
    | true =>
      simp only [d9994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9995 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9996 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9997 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9998 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9999 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23517 (p : Pattern) (ha : d101949 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9882 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23512 q ha hb
    | true =>
      simp only [d9882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23513 q ha hb
  have h2 (q : Pattern) (ha : d101945 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10000 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23516 q ha hb
    | true =>
      simp only [d10000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10001 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d101946 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101947 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101948 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101949 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23518 (p : Pattern) (ha : d101955 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101950 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23517 q ha hb
  have h2 (q : Pattern) (ha : d10017 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23505 q ha hb
  have h3 (q : Pattern) (ha : d101951 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101952 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d101953 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101954 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d101955 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23519 (p : Pattern) (ha : d101961 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101956 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23518 q ha hb
  have h2 (q : Pattern) (ha : d101957 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101958 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101959 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101960 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101961 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23520 (p : Pattern) (ha : d10121 p = 1) (hb : d102051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1569 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1570 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1570, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1570, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10111 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1571 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10112 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10113 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d10114 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d10115 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10115, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d10115, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d10116 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10117 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d10118 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10119 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d10120 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d10084 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d10085 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d10085, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d10086 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d10087 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d10088 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d10089 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d10089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d10105 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d10105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d10121 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro23521 (p : Pattern) (ha : d10163 p = 1) (hb : d102051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1581 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1582 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1582, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10159 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1583 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10160 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10161 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10162 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10134 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d10135 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d10135, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d10136 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10137 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d10138 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10139 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d10140 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d10163 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro23522 (p : Pattern) (ha : d10169 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10164 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23520 q ha hb
    | true =>
      simp only [d10164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23521 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10165 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10165, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10165, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10166 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10167 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10168 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10169 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23523 (p : Pattern) (ha : d10316 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10170 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23522 q ha hb
    | true =>
      simp only [d10170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10171 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10313 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10314 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10315 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10316 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23524 (p : Pattern) (ha : d10322 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10317 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23523 q ha hb
    | true =>
      simp only [d10317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10318 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10319 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10320 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10321 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10322 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23525 (p : Pattern) (ha : d10069 p = 1) (hb : d102051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1664 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1665 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1665, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1665, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10032 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1666 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10033 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10034 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d10035 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d10036 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10036, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d10036, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d10037 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10038 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d10039 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10040 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d10041 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d10045 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d10046 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10046, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d10046, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d10047 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d10048 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d10049 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d10050 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d10050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d0 q = 1) (hb : d10062 q = 1) : d0 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d10063 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10063, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d10063, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h23 (q : Pattern) (ha : d10064 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d10065 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d10065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d10066 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d10066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d10067 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d10067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d10068 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d10068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d10069 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  exact h28 p ha hb
theorem andIntro23526 (p : Pattern) (ha : d10091 p = 1) (hb : d102051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1554 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1555 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1555, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1555, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10070 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1556 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10071 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10072 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d10073 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d10074 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10074, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d10074, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d10075 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10076 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d10077 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10078 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d10079 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d10062 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d10063 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10063, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d10063, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d10064 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d10065 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d10066 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d10067 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d10067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d0 q = 1) (hb : d10084 q = 1) : d0 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d10085 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d10085, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h23 (q : Pattern) (ha : d10086 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d10087 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d10087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d10088 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d10088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d10089 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d10089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d10090 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d10090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d10091 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  exact h28 p ha hb
theorem andIntro23527 (p : Pattern) (ha : d10106 p = 1) (hb : d102051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10098 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10099 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10099, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d10099, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10100 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10101 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10102 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10103 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d10084 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d10085 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10085, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d10085, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d10086 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10087 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d10088 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10089 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d10104 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d10105 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d10106 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro23528 (p : Pattern) (ha : d10141 p = 1) (hb : d102051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5133 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5134 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5134, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d5134, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10125 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5135 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10126 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10127 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10128 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10134 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d10135 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d10135, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d10136 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10137 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d10138 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10139 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d10140 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d10141 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro23529 (p : Pattern) (ha : d10147 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10092 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23525 q ha hb
    | true =>
      simp only [d10092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23526 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10093 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10093, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10093, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10094 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10107 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23526 q ha hb
    | true =>
      simp only [d10107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23527 q ha hb
  have h6 (q : Pattern) (ha : d10108 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10108, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10108, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d10109 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10110 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10122 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23526 q ha hb
    | true =>
      simp only [d10122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23520 q ha hb
  have h10 (q : Pattern) (ha : d10123 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10123, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d10124 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10142 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23520 q ha hb
    | true =>
      simp only [d10142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23528 q ha hb
  have h13 (q : Pattern) (ha : d10143 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10143, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d10144 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d10145 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10146 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10147 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro23530 (p : Pattern) (ha : d10152 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10122 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23526 q ha hb
    | true =>
      simp only [d10122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23520 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10123 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10123, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10124 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10142 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23520 q ha hb
    | true =>
      simp only [d10142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23528 q ha hb
  have h6 (q : Pattern) (ha : d10143 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10143, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d10144 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10145 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10150 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10151 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10152 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro23531 (p : Pattern) (ha : d10158 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10148 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23529 q ha hb
    | true =>
      simp only [d10148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10149 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10153 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23530 q ha hb
    | true =>
      simp only [d10153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10154 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10155 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10156 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10157 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10158 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23532 (p : Pattern) (ha : d10175 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10153 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23530 q ha hb
    | true =>
      simp only [d10153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10154 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10170 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23522 q ha hb
    | true =>
      simp only [d10170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10171 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10172 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10173 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10174 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10175 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23533 (p : Pattern) (ha : d10293 p = 1) (hb : d102051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1581 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1582 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1582, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1582, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10159 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1583 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10160 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10161 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10162 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d10293 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro23534 (p : Pattern) (ha : d10299 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10122 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23526 q ha hb
    | true =>
      simp only [d10122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23520 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10123 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10123, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10124 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10142 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23520 q ha hb
    | true =>
      simp only [d10142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23528 q ha hb
  have h6 (q : Pattern) (ha : d10143 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10143, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d10144 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10145 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10294 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23520 q ha hb
    | true =>
      simp only [d10294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23533 q ha hb
  have h10 (q : Pattern) (ha : d10295 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10295, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10295, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d10296 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10297 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d10298 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10299 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro23535 (p : Pattern) (ha : d10305 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10300 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23534 q ha hb
    | true =>
      simp only [d10300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10301 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10302 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10303 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10304 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10305 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23536 (p : Pattern) (ha : d101969 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10176 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23531 q ha hb
    | true =>
      simp only [d10176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23532 q ha hb
  have h2 (q : Pattern) (ha : d101965 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10306 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23535 q ha hb
    | true =>
      simp only [d10306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10307 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d101966 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101967 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101968 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101969 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23537 (p : Pattern) (ha : d101975 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101970 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23536 q ha hb
  have h2 (q : Pattern) (ha : d10323 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23524 q ha hb
  have h3 (q : Pattern) (ha : d101971 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101972 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d101973 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101974 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d101975 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23538 (p : Pattern) (ha : d101981 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101976 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23537 q ha hb
  have h2 (q : Pattern) (ha : d101977 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101978 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101979 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101980 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101981 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23539 (p : Pattern) (ha : d10397 p = 1) (hb : d102051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2053 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2053, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10387 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2054 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10388 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10389 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d10390 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d10391 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10391, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d10391, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d10392 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10393 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d10394 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10395 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d10396 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d10370 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d10371 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d10371, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d10372 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d10373 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d10374 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d10375 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d10375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d10381 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d10381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d10397 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro23540 (p : Pattern) (ha : d10440 p = 1) (hb : d102051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2064 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2065 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2065, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10436 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2066 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10437 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10438 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10439 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10411 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d10412 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d10412, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d10413 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10414 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d10415 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10416 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d10417 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d10440 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro23541 (p : Pattern) (ha : d10446 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10441 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23539 q ha hb
    | true =>
      simp only [d10441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23540 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10442 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10442, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10442, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10443 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10444 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10445 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10446 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23542 (p : Pattern) (ha : d10582 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10447 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23541 q ha hb
    | true =>
      simp only [d10447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10448 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10579 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10580 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10581 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10582 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23543 (p : Pattern) (ha : d10588 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10583 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23542 q ha hb
    | true =>
      simp only [d10583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10584 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10585 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10586 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10587 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10588 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23544 (p : Pattern) (ha : d10359 p = 1) (hb : d102051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2143 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2144 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2144, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2144, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10339 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2145 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10340 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10341 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d10342 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d10343 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10343, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d10343, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d10344 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10345 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d10346 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10347 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d10348 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d10352 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d10353 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d10353, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d10354 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d10355 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d10356 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d10357 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d10357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d10358 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d10359 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro23545 (p : Pattern) (ha : d10377 p = 1) (hb : d102051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2034 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2035 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2035, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10360 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2036 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10361 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10362 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d10363 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d10364 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d10364, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d10365 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10366 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d10367 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10368 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d10369 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d10352 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d10353 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d10353, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d10354 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d10355 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d10355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d10356 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d10357 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d10357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d0 q = 1) (hb : d10370 q = 1) : d0 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d10371 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d10371, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h23 (q : Pattern) (ha : d10372 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d10373 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d10373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d10374 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d10374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d10375 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d10375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d10376 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d10376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d10377 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  exact h28 p ha hb
theorem andIntro23546 (p : Pattern) (ha : d10382 p = 1) (hb : d102051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10352 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10353 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d10353, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10354 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10355 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10356 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10357 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d10370 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d10371 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10371, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d10371, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d10372 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10373 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d10374 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10375 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d10376 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d10381 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d10382 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro23547 (p : Pattern) (ha : d10418 p = 1) (hb : d102051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5246 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d5247 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5247, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d5247, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10401 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5248 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10402 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10403 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10404 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10411 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d10412 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d10412, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d10413 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10414 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d10415 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10416 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d10416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d10417 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d10417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d10418 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro23548 (p : Pattern) (ha : d10424 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10378 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23544 q ha hb
    | true =>
      simp only [d10378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23545 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10379 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10379, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10379, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10380 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10383 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23545 q ha hb
    | true =>
      simp only [d10383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23546 q ha hb
  have h6 (q : Pattern) (ha : d10384 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10384, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10384, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d10385 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10386 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10398 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23545 q ha hb
    | true =>
      simp only [d10398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23539 q ha hb
  have h10 (q : Pattern) (ha : d10399 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10399, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d10400 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10419 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23539 q ha hb
    | true =>
      simp only [d10419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23547 q ha hb
  have h13 (q : Pattern) (ha : d10420 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10420, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d10421 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d10422 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10423 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10424 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro23549 (p : Pattern) (ha : d10429 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10398 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23545 q ha hb
    | true =>
      simp only [d10398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23539 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10399 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10399, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10400 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10419 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23539 q ha hb
    | true =>
      simp only [d10419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23547 q ha hb
  have h6 (q : Pattern) (ha : d10420 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10420, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d10421 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10422 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10427 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d10428 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10429 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro23550 (p : Pattern) (ha : d10435 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10425 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23548 q ha hb
    | true =>
      simp only [d10425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10426 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10430 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23549 q ha hb
    | true =>
      simp only [d10430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10431 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10432 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10433 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10434 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10435 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23551 (p : Pattern) (ha : d10452 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10430 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23549 q ha hb
    | true =>
      simp only [d10430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10431 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10447 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23541 q ha hb
    | true =>
      simp only [d10447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10448 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10449 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10450 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10451 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10452 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23552 (p : Pattern) (ha : d10559 p = 1) (hb : d102051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2064 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2065 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2065, d102051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10436 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2066 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10437 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d10437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10438 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d10438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10439 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d10439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d10559 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d10559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro23553 (p : Pattern) (ha : d10565 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10398 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23545 q ha hb
    | true =>
      simp only [d10398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23539 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10399 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10399, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10400 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10419 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23539 q ha hb
    | true =>
      simp only [d10419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23547 q ha hb
  have h6 (q : Pattern) (ha : d10420 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10420, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d10421 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10422 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10560 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23539 q ha hb
    | true =>
      simp only [d10560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23552 q ha hb
  have h10 (q : Pattern) (ha : d10561 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10561, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10561, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d10562 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10563 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d10564 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10565 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro23554 (p : Pattern) (ha : d10571 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10566 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23553 q ha hb
    | true =>
      simp only [d10566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10567 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10568 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10569 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10570 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10571 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23555 (p : Pattern) (ha : d101990 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10453 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23550 q ha hb
    | true =>
      simp only [d10453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23551 q ha hb
  have h2 (q : Pattern) (ha : d101986 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10572 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23554 q ha hb
    | true =>
      simp only [d10572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10573 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d101987 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101988 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101989 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101990 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23556 (p : Pattern) (ha : d101996 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101991 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23555 q ha hb
  have h2 (q : Pattern) (ha : d10589 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23543 q ha hb
  have h3 (q : Pattern) (ha : d101992 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101993 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d101994 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101995 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d101996 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23557 (p : Pattern) (ha : d102002 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101997 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23556 q ha hb
  have h2 (q : Pattern) (ha : d101998 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101999 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d102000 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d102000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102001 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d102001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102002 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d102002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23558 (p : Pattern) (ha : d102008 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d101925 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23471 q ha hb
    | true =>
      simp only [d101925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23484 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d101943 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23500 q ha hb
  have h3 (q : Pattern) (ha : d101944 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d101944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101962 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23519 q ha hb
  have h5 (q : Pattern) (ha : d101963 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d101963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101964 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d101964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101982 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23538 q ha hb
  have h8 (q : Pattern) (ha : d101983 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d101983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d101984 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d101984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d101985 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d101985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d101985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d102003 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d102003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23557 q ha hb
  have h12 (q : Pattern) (ha : d102004 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d102004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d102005 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d102005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d102006 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d102006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d102007 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d102007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d102007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d102008 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d102008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d102008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro23559 (p : Pattern) (ha : d102014 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102009 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d102009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23558 q ha hb
    | true =>
      simp only [d102009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d102010 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d102010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d102011 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d102011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102012 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d102012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102013 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d102013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d102014 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d102014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23560 (p : Pattern) (ha : d102020 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102015 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d102015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23559 q ha hb
    | true =>
      simp only [d102015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d102016 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d102016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d102017 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d102017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102018 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d102018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102019 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d102019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d102020 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d102020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23561 (p : Pattern) (ha : d102026 p = 1) (hb : d130390 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102021 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d102021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23560 q ha hb
    | true =>
      simp only [d102021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d102022 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d102022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d102023 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d102023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d102024 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d102024, d130390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102024, d130390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d102025 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d102025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d102026 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d102026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d102026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro23562 (p : Pattern) (ha : d102032 p = 1) (hb : d130390 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102027 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d102027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23561 q ha hb
    | true =>
      simp only [d102027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d102028 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d102028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d102029 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d102029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102030 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d102030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102031 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d102031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d102032 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d102032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23563 (p : Pattern) (ha : d102038 p = 1) (hb : d130390 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102033 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d102033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23562 q ha hb
    | true =>
      simp only [d102033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d102034 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d102034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d102035 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d102035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102036 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d102036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102037 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d102037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d102038 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d102038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23564 (p : Pattern) (ha : d102044 p = 1) (hb : d130390 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102039 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d102039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23563 q ha hb
    | true =>
      simp only [d102039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d102040 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d102040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d102041 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d102041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102042 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d102042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102043 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d102043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d102044 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d102044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23565 (p : Pattern) (ha : d102050 p = 1) (hb : d130390 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102045 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d102045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23564 q ha hb
    | true =>
      simp only [d102045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d102046 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d102046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d102047 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d102047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102048 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d102048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102049 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d102049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d102050 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d102050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23566 (p : Pattern) (ha : d129477 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9437 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23464 q ha hb
  have h2 (q : Pattern) (ha : d129473 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129474 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129475 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129476 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129477 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23567 (p : Pattern) (ha : d129487 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9342 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23461 q ha hb
    | true =>
      simp only [d9342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23456 q ha hb
  have h2 (q : Pattern) (ha : d129483 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129484 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129485 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129486 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129487 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23568 (p : Pattern) (ha : d129493 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129488 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23567 q ha hb
  have h2 (q : Pattern) (ha : d129489 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129490 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129491 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129492 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129493 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23569 (p : Pattern) (ha : d129499 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129478 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23566 q ha hb
  have h2 (q : Pattern) (ha : d129479 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129480 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129481 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129482 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129494 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23568 q ha hb
  have h7 (q : Pattern) (ha : d129495 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129496 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129497 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129498 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d129499 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro23570 (p : Pattern) (ha : d129505 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129500 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23480 q ha hb
    | true =>
      simp only [d129500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23473 q ha hb
  have h2 (q : Pattern) (ha : d129501 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129502 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129503 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129504 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129505 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23571 (p : Pattern) (ha : d129511 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129506 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23570 q ha hb
  have h2 (q : Pattern) (ha : d129507 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129508 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129509 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129510 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129511 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23572 (p : Pattern) (ha : d129517 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129512 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23571 q ha hb
  have h2 (q : Pattern) (ha : d129513 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129514 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129515 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129516 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129517 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23573 (p : Pattern) (ha : d129524 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129519 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23496 q ha hb
    | true =>
      simp only [d129519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23488 q ha hb
  have h2 (q : Pattern) (ha : d129520 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129521 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129522 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129523 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129524 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23574 (p : Pattern) (ha : d129530 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129525 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23573 q ha hb
  have h2 (q : Pattern) (ha : d129526 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129527 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129528 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129529 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129530 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23575 (p : Pattern) (ha : d129536 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129531 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23574 q ha hb
  have h2 (q : Pattern) (ha : d129532 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129533 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129534 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129535 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129536 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23576 (p : Pattern) (ha : d129540 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9834 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23507 q ha hb
    | true =>
      simp only [d9834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23501 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9835 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9835, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9835, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9836 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9851 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23501 q ha hb
    | true =>
      simp only [d9851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23509 q ha hb
  have h6 (q : Pattern) (ha : d9852 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9852, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9852, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d9853 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9854 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9870 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23501 q ha hb
    | true =>
      simp only [d9870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23502 q ha hb
  have h10 (q : Pattern) (ha : d9871 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9871, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9871, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d9872 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9873 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d129539 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d129539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d129539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d129540 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d129540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro23577 (p : Pattern) (ha : d129546 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129541 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23576 q ha hb
    | true =>
      simp only [d129541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129542 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9876 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23503 q ha hb
    | true =>
      simp only [d9876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9877 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129543 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d129543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129544 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d129544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129545 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d129545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d129546 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d129546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d129546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23578 (p : Pattern) (ha : d129552 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129547 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23577 q ha hb
    | true =>
      simp only [d129547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23504 q ha hb
  have h2 (q : Pattern) (ha : d129548 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129549 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129550 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129551 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129552 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23579 (p : Pattern) (ha : d129558 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129553 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23578 q ha hb
  have h2 (q : Pattern) (ha : d129554 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129555 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129556 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129557 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129558 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23580 (p : Pattern) (ha : d129564 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129559 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23579 q ha hb
  have h2 (q : Pattern) (ha : d129560 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129561 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129562 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129563 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129564 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23581 (p : Pattern) (ha : d129569 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10122 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23526 q ha hb
    | true =>
      simp only [d10122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23520 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10123 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10123, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10124 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10142 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23520 q ha hb
    | true =>
      simp only [d10142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23528 q ha hb
  have h6 (q : Pattern) (ha : d10143 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10143, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d10144 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10145 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10164 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23520 q ha hb
    | true =>
      simp only [d10164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23521 q ha hb
  have h10 (q : Pattern) (ha : d10165 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10165, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10165, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d10166 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10167 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d129568 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d129568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d129568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d129569 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d129569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro23582 (p : Pattern) (ha : d129575 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129570 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23581 q ha hb
    | true =>
      simp only [d129570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129571 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10170 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23522 q ha hb
    | true =>
      simp only [d10170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10171 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129572 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d129572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129573 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d129573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129574 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d129574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d129575 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d129575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d129575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23583 (p : Pattern) (ha : d129581 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129576 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23582 q ha hb
    | true =>
      simp only [d129576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23523 q ha hb
  have h2 (q : Pattern) (ha : d129577 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129578 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129579 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129580 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129581 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23584 (p : Pattern) (ha : d129587 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129582 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23583 q ha hb
  have h2 (q : Pattern) (ha : d129583 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129584 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129585 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129586 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129587 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23585 (p : Pattern) (ha : d129593 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129588 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23584 q ha hb
  have h2 (q : Pattern) (ha : d129589 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129590 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129591 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129592 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129593 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23586 (p : Pattern) (ha : d129599 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10398 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23545 q ha hb
    | true =>
      simp only [d10398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23539 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d10399 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10399, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10400 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10419 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23539 q ha hb
    | true =>
      simp only [d10419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23547 q ha hb
  have h6 (q : Pattern) (ha : d10420 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10420, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d10421 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10422 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10441 q = 1) (hb : d102051 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23539 q ha hb
    | true =>
      simp only [d10441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23540 q ha hb
  have h10 (q : Pattern) (ha : d10442 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10442, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10442, d130389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d10443 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10444 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d129598 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d129598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d129598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d129599 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d129599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro23587 (p : Pattern) (ha : d129605 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129600 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23586 q ha hb
    | true =>
      simp only [d129600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129601 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10447 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23541 q ha hb
    | true =>
      simp only [d10447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10448 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129602 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d129602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129603 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d129603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129604 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d129604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d129605 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d129605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d129605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23588 (p : Pattern) (ha : d129611 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129606 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23587 q ha hb
    | true =>
      simp only [d129606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23542 q ha hb
  have h2 (q : Pattern) (ha : d129607 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129608 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129609 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129610 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129611 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23589 (p : Pattern) (ha : d129617 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129612 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23588 q ha hb
  have h2 (q : Pattern) (ha : d129613 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129614 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129615 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129616 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129617 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23590 (p : Pattern) (ha : d129623 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129618 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23589 q ha hb
  have h2 (q : Pattern) (ha : d129619 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129620 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129621 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129622 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129623 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23591 (p : Pattern) (ha : d129629 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d129518 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23569 q ha hb
    | true =>
      simp only [d129518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23572 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d129537 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23575 q ha hb
  have h3 (q : Pattern) (ha : d129538 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129565 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23580 q ha hb
  have h5 (q : Pattern) (ha : d129566 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129567 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129594 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23585 q ha hb
  have h8 (q : Pattern) (ha : d129595 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129596 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129597 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d129597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d129624 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23590 q ha hb
  have h12 (q : Pattern) (ha : d129625 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d129626 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d129627 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d129627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d129628 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d129628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d129628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d129629 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d129629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d129629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro23592 (p : Pattern) (ha : d129635 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129630 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d129630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23591 q ha hb
    | true =>
      simp only [d129630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129631 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d129631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129632 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d129632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129633 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d129633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129634 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d129634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129635 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d129635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23593 (p : Pattern) (ha : d129641 p = 1) (hb : d130389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129636 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d129636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23592 q ha hb
    | true =>
      simp only [d129636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129637 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d129637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129638 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d129638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129639 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d129639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129640 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d129640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129641 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d129641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23594 (p : Pattern) (ha : d129647 p = 1) (hb : d130390 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129642 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d129642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23593 q ha hb
    | true =>
      simp only [d129642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129643 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d129643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129644 q = 1) (hb : d130389 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d129644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d129645 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d129645, d130390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129645, d130390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d129646 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d129646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129647 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d129647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d129647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h8 p ha hb
theorem andIntro23595 (p : Pattern) (ha : d129653 p = 1) (hb : d130390 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129648 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d129648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23594 q ha hb
    | true =>
      simp only [d129648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129649 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d129649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129650 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d129650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129651 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d129651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129652 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d129652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129653 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d129653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23596 (p : Pattern) (ha : d129659 p = 1) (hb : d130390 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129654 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d129654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23595 q ha hb
    | true =>
      simp only [d129654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129655 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d129655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129656 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d129656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129657 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d129657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129658 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d129658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129659 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d129659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23597 (p : Pattern) (ha : d129665 p = 1) (hb : d130390 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129660 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d129660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23596 q ha hb
    | true =>
      simp only [d129660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129661 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d129661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129662 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d129662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129663 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d129663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129664 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d129664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129665 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d129665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23598 (p : Pattern) (ha : d129671 p = 1) (hb : d130390 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129666 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d129666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23597 q ha hb
    | true =>
      simp only [d129666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129667 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d129667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129668 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d129668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129669 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d129669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129670 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d129670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129671 q = 1) (hb : d130390 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d129671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23599 (p : Pattern) (ha : d102038 p = 1) (hb : d102105 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102033 q = 1) (hb : d102105 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d102033, d102105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23207 q hb ha
    | true =>
      simp only [d102033, d102105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d102105 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d102034 q = 1) (hb : d102105 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d102034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d102035 q = 1) (hb : d102105 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d102035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h5 (q : Pattern) (ha : d102036 q = 1) (hb : d102105 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d102036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d102037 q = 1) (hb : d102105 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d102037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d102038 q = 1) (hb : d102105 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d102038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d102038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  exact h7 p ha hb
theorem andIntro23600 (p : Pattern) (ha : d102044 p = 1) (hb : d102105 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102105 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102039 q = 1) (hb : d102105 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d102039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23599 q ha hb
    | true =>
      simp only [d102039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d102040 q = 1) (hb : d102105 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d102040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d102041 q = 1) (hb : d102105 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d102041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102042 q = 1) (hb : d102105 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d102042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102043 q = 1) (hb : d102105 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d102043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d102044 q = 1) (hb : d102105 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d102044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23601 (p : Pattern) (ha : d102050 p = 1) (hb : d102105 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102105 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102045 q = 1) (hb : d102105 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d102045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23600 q ha hb
    | true =>
      simp only [d102045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d102046 q = 1) (hb : d102105 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d102046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d102047 q = 1) (hb : d102105 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d102047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102048 q = 1) (hb : d102105 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d102048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102049 q = 1) (hb : d102105 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d102049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d102050 q = 1) (hb : d102105 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d102050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23602 (p : Pattern) (ha : d102105 p = 1) (hb : d129659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102105 q = 1) (hb : d129654 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d102105, d129654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23240 q ha hb
    | true =>
      simp only [d102105, d129654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d102105 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d102105 q = 1) (hb : d129655 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d129655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d102105 q = 1) (hb : d129656 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d129656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h5 (q : Pattern) (ha : d102105 q = 1) (hb : d129657 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d129657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h6 (q : Pattern) (ha : d102105 q = 1) (hb : d129658 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d129658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h7 (q : Pattern) (ha : d102105 q = 1) (hb : d129659 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d129659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  exact h7 p ha hb
theorem andIntro23603 (p : Pattern) (ha : d102105 p = 1) (hb : d129665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102105 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102105 q = 1) (hb : d129660 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d129660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23602 q ha hb
    | true =>
      simp only [d129660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d102105 q = 1) (hb : d129661 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d129661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d102105 q = 1) (hb : d129662 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d129662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102105 q = 1) (hb : d129663 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d129663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102105 q = 1) (hb : d129664 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d129664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102105 q = 1) (hb : d129665 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d129665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23604 (p : Pattern) (ha : d102105 p = 1) (hb : d129671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d102105 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102105 q = 1) (hb : d129666 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d129666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23603 q ha hb
    | true =>
      simp only [d129666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d102105 q = 1) (hb : d129667 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d129667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d102105 q = 1) (hb : d129668 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d129668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d102105 q = 1) (hb : d129669 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d129669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d102105 q = 1) (hb : d129670 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d129670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d102105 q = 1) (hb : d129671 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d129671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23605 (p : Pattern) (ha : d100942 p = 1) (hb : d102038 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d102033 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d102033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23207 q ha hb
    | true =>
      simp only [d102033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d100942 q = 1) (hb : d102034 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d100942, d102034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d100942, d102034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d100942 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d100942 q = 1) (hb : d102035 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d102035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d100942 q = 1) (hb : d102036 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d102036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h7 (q : Pattern) (ha : d100942 q = 1) (hb : d102037 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d102037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d102037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h8 (q : Pattern) (ha : d100942 q = 1) (hb : d102038 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d102038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d102038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  exact h8 p ha hb
theorem andIntro23606 (p : Pattern) (ha : d100942 p = 1) (hb : d102044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100942 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100942 q = 1) (hb : d102039 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d102039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23605 q ha hb
    | true =>
      simp only [d102039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d100942 q = 1) (hb : d102040 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d102040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d100942 q = 1) (hb : d102041 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d102041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d100942 q = 1) (hb : d102042 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d102042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d100942 q = 1) (hb : d102043 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d102043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d100942 q = 1) (hb : d102044 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d102044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23607 (p : Pattern) (ha : d100942 p = 1) (hb : d102050 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100942 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100942 q = 1) (hb : d102045 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d102045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23606 q ha hb
    | true =>
      simp only [d102045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d100942 q = 1) (hb : d102046 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d102046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d100942 q = 1) (hb : d102047 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d102047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d100942 q = 1) (hb : d102048 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d102048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d100942 q = 1) (hb : d102049 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d102049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d100942 q = 1) (hb : d102050 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d102050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23608 (p : Pattern) (ha : d100942 p = 1) (hb : d129659 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100941 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100941 q = 1) (hb : d129654 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d129654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23240 q ha hb
    | true =>
      simp only [d129654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d100942 q = 1) (hb : d129655 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d100942, d129655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d100942, d129655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d100942 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d100942 q = 1) (hb : d129656 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d129656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d100942 q = 1) (hb : d129657 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d129657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h7 (q : Pattern) (ha : d100942 q = 1) (hb : d129658 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d129658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h8 (q : Pattern) (ha : d100942 q = 1) (hb : d129659 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d129659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d129659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  exact h8 p ha hb
theorem andIntro23609 (p : Pattern) (ha : d100942 p = 1) (hb : d129665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100942 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100942 q = 1) (hb : d129660 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d129660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23608 q ha hb
    | true =>
      simp only [d129660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d100942 q = 1) (hb : d129661 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d129661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d100942 q = 1) (hb : d129662 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d129662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d100942 q = 1) (hb : d129663 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d129663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d100942 q = 1) (hb : d129664 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d129664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d100942 q = 1) (hb : d129665 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d129665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23610 (p : Pattern) (ha : d100942 p = 1) (hb : d129671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d100942 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d100942 q = 1) (hb : d129666 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d129666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23609 q ha hb
    | true =>
      simp only [d129666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d100942 q = 1) (hb : d129667 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d129667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d100942 q = 1) (hb : d129668 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d129668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d100942 q = 1) (hb : d129669 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d129669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d100942 q = 1) (hb : d129670 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d129670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d100942 q = 1) (hb : d129671 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d129671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro23611 (p : Pattern) (ha : d102050 p = 1) (hb : d130482 p = 1) : d102050 p = 1 := by
  have h0 (q : Pattern) (ha : d102050 q = 1) (hb : d130482 q = 1) : d102050 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro23612 (p : Pattern) (ha : d9302 p = 1) (hb : d130483 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51928 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9297 q = 1) (hb : d100948 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
    | true =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9298 q = 1) (hb : d100949 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9298, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9298, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d9299 q = 1) (hb : d100950 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9299, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9299, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9300 q = 1) (hb : d100951 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9300, d100951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9300, d100951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d9301 q = 1) (hb : d100952 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9301, d100952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9301, d100952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d9302 q = 1) (hb : d130483 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9302, d130483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9302, d130483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23613 (p : Pattern) (ha : d9308 p = 1) (hb : d130489 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9303 q = 1) (hb : d130484 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9303, d130484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23612 q ha hb
    | true =>
      simp only [d9303, d130484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9304 q = 1) (hb : d130485 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9304, d130485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9304, d130485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9305 q = 1) (hb : d130486 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9305, d130486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9305, d130486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9306 q = 1) (hb : d130487 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9306, d130487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9306, d130487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9307 q = 1) (hb : d130488 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9307, d130488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9307, d130488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9308 q = 1) (hb : d130489 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9308, d130489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9308, d130489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23614 (p : Pattern) (ha : d9314 p = 1) (hb : d130495 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9309 q = 1) (hb : d130490 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9309, d130490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23613 q ha hb
    | true =>
      simp only [d9309, d130490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9310 q = 1) (hb : d130491 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9310, d130491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9310, d130491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9311 q = 1) (hb : d130492 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9311, d130492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9311, d130492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9312 q = 1) (hb : d130493 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9312, d130493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9312, d130493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9313 q = 1) (hb : d130494 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9313, d130494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9313, d130494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9314 q = 1) (hb : d130495 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9314, d130495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9314, d130495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23615 (p : Pattern) (ha : d9320 p = 1) (hb : d130501 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9315 q = 1) (hb : d130496 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9315, d130496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9315, d130496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23614 q ha hb
  have h2 (q : Pattern) (ha : d9316 q = 1) (hb : d130497 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d9316, d130497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9316, d130497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9317 q = 1) (hb : d130498 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d9317, d130498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9317, d130498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9318 q = 1) (hb : d130499 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d9318, d130499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9318, d130499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9319 q = 1) (hb : d130500 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d9319, d130500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9319, d130500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9320 q = 1) (hb : d130501 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d9320, d130501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9320, d130501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23616 (p : Pattern) (ha : d9335 p = 1) (hb : d130506 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52054 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9330 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
    | true =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
  have h3 (q : Pattern) (ha : d9331 q = 1) (hb : d100982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d9332 q = 1) (hb : d100983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9297 q = 1) (hb : d100948 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
    | true =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d9298 q = 1) (hb : d100949 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9298, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9298, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d9299 q = 1) (hb : d100950 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9299, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9299, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9333 q = 1) (hb : d100984 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9333, d100984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9333, d100984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9300 q = 1) (hb : d100951 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9300, d100951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9300, d100951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d9334 q = 1) (hb : d100985 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9334, d100985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9334, d100985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9335 q = 1) (hb : d130506 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9335, d130506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9335, d130506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro23617 (p : Pattern) (ha : d9341 p = 1) (hb : d130512 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9336 q = 1) (hb : d130507 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9336, d130507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23616 q ha hb
    | true =>
      simp only [d9336, d130507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9337 q = 1) (hb : d130508 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9337, d130508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9337, d130508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9303 q = 1) (hb : d130484 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9303, d130484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23612 q ha hb
    | true =>
      simp only [d9303, d130484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9304 q = 1) (hb : d130485 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9304, d130485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9304, d130485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9338 q = 1) (hb : d130509 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9338, d130509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9338, d130509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9339 q = 1) (hb : d130510 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9339, d130510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9339, d130510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9340 q = 1) (hb : d130511 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9340, d130511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9340, d130511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9341 q = 1) (hb : d130512 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9341, d130512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9341, d130512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23618 (p : Pattern) (ha : d101879 p = 1) (hb : d130518 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9342 q = 1) (hb : d130513 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9342, d130513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23617 q ha hb
    | true =>
      simp only [d9342, d130513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23613 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130490 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101875 q = 1) (hb : d130514 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101875, d130514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101875, d130514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9309 q = 1) (hb : d130490 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9309, d130490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23613 q ha hb
    | true =>
      simp only [d9309, d130490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9310 q = 1) (hb : d130491 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9310, d130491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9310, d130491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101876 q = 1) (hb : d130515 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101876, d130515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101876, d130515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101877 q = 1) (hb : d130516 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101877, d130516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101877, d130516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101878 q = 1) (hb : d130517 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101878, d130517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101878, d130517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d101879 q = 1) (hb : d130518 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101879, d130518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101879, d130518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro23619 (p : Pattern) (ha : d101885 p = 1) (hb : d130524 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101880 q = 1) (hb : d130519 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101880, d130519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101880, d130519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23618 q ha hb
  have h2 (q : Pattern) (ha : d101881 q = 1) (hb : d130520 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101881, d130520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101881, d130520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d101882 q = 1) (hb : d130521 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101882, d130521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d101882, d130521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d101883 q = 1) (hb : d130522 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101883, d130522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101883, d130522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d101884 q = 1) (hb : d130523 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101884, d130523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101884, d130523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101885 q = 1) (hb : d130524 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101885, d130524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101885, d130524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23620 (p : Pattern) (ha : d9436 p = 1) (hb : d130554 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9309 q = 1) (hb : d130490 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9309, d130490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23613 q ha hb
    | true =>
      simp only [d9309, d130490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9432 q = 1) (hb : d130550 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9432, d130550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9432, d130550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9433 q = 1) (hb : d130551 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9433, d130551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9433, d130551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9434 q = 1) (hb : d130552 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9434, d130552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9434, d130552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9435 q = 1) (hb : d130553 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9435, d130553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9435, d130553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9436 q = 1) (hb : d130554 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9436, d130554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9436, d130554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23621 (p : Pattern) (ha : d9394 p = 1) (hb : d130530 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d126917 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9389 q = 1) (hb : d101022 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23262 q ha hb
    | true =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
  have h3 (q : Pattern) (ha : d9390 q = 1) (hb : d101023 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9390, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9390, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d9391 q = 1) (hb : d101024 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9391, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9391, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9330 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
    | true =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
  have h6 (q : Pattern) (ha : d9331 q = 1) (hb : d100982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d9332 q = 1) (hb : d100983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9392 q = 1) (hb : d101025 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9392, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9392, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9297 q = 1) (hb : d100948 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
    | true =>
      simp only [d9297, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d9298 q = 1) (hb : d100949 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9298, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9298, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d9299 q = 1) (hb : d100950 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9299, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9299, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9333 q = 1) (hb : d100984 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9333, d100984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9333, d100984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9393 q = 1) (hb : d101026 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9393, d101026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9393, d101026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9394 q = 1) (hb : d130530 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9394, d130530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9394, d130530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro23622 (p : Pattern) (ha : d9400 p = 1) (hb : d130536 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9395 q = 1) (hb : d130531 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9395, d130531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23621 q ha hb
    | true =>
      simp only [d9395, d130531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9396 q = 1) (hb : d130532 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9396, d130532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9396, d130532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9336 q = 1) (hb : d130507 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9336, d130507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23616 q ha hb
    | true =>
      simp only [d9336, d130507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9337 q = 1) (hb : d130508 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9337, d130508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9337, d130508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9397 q = 1) (hb : d130533 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9397, d130533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9397, d130533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9398 q = 1) (hb : d130534 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9398, d130534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9398, d130534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9399 q = 1) (hb : d130535 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9399, d130535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9399, d130535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9400 q = 1) (hb : d130536 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9400, d130536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9400, d130536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23623 (p : Pattern) (ha : d9424 p = 1) (hb : d130542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9336 q = 1) (hb : d130507 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9336, d130507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23616 q ha hb
    | true =>
      simp only [d9336, d130507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9337 q = 1) (hb : d130508 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9337, d130508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9337, d130508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9421 q = 1) (hb : d130539 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9421, d130539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9421, d130539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9422 q = 1) (hb : d130540 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9422, d130540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9422, d130540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9423 q = 1) (hb : d130541 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9423, d130541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9423, d130541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9424 q = 1) (hb : d130542 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9424, d130542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9424, d130542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23624 (p : Pattern) (ha : d101895 p = 1) (hb : d130548 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9401 q = 1) (hb : d130537 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9401, d130537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23622 q ha hb
    | true =>
      simp only [d9401, d130537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23617 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130513 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101891 q = 1) (hb : d130538 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101891, d130538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101891, d130538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9425 q = 1) (hb : d130543 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9425, d130543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23623 q ha hb
    | true =>
      simp only [d9425, d130543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9426 q = 1) (hb : d130544 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9426, d130544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9426, d130544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101892 q = 1) (hb : d130545 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101892, d130545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101892, d130545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101893 q = 1) (hb : d130546 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101893, d130546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101893, d130546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101894 q = 1) (hb : d130547 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101894, d130547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101894, d130547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d101895 q = 1) (hb : d130548 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101895, d130548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101895, d130548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro23625 (p : Pattern) (ha : d101901 p = 1) (hb : d130560 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101896 q = 1) (hb : d130549 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101896, d130549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101896, d130549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23624 q ha hb
  have h2 (q : Pattern) (ha : d9437 q = 1) (hb : d130555 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9437, d130555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9437, d130555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23620 q ha hb
  have h3 (q : Pattern) (ha : d101897 q = 1) (hb : d130556 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101897, d130556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101897, d130556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101898 q = 1) (hb : d130557 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101898, d130557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101898, d130557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d101899 q = 1) (hb : d130558 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101899, d130558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101899, d130558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101900 q = 1) (hb : d130559 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101900, d130559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101900, d130559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d101901 q = 1) (hb : d130560 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101901, d130560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101901, d130560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23626 (p : Pattern) (ha : d101907 p = 1) (hb : d130566 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9321 q = 1) (hb : d130502 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d9321, d130502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9321, d130502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23615 q ha hb
  have h2 (q : Pattern) (ha : d9322 q = 1) (hb : d130503 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d9322, d130503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9322, d130503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9323 q = 1) (hb : d130504 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d9323, d130504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9323, d130504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9324 q = 1) (hb : d130505 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d9324, d130505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9324, d130505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101886 q = 1) (hb : d130525 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101886, d130525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101886, d130525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23619 q ha hb
  have h6 (q : Pattern) (ha : d101887 q = 1) (hb : d130526 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101887, d130526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101887, d130526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101888 q = 1) (hb : d130527 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101888, d130527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101888, d130527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101889 q = 1) (hb : d130528 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101889, d130528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101889, d130528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d101890 q = 1) (hb : d130529 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101890, d130529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101890, d130529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d101902 q = 1) (hb : d130561 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101902, d130561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101902, d130561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23625 q ha hb
  have h11 (q : Pattern) (ha : d101903 q = 1) (hb : d130562 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101903, d130562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101903, d130562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d101904 q = 1) (hb : d130563 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101904, d130563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101904, d130563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d101905 q = 1) (hb : d130564 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101905, d130564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101905, d130564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d101906 q = 1) (hb : d130565 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101906, d130565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101906, d130565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d101907 q = 1) (hb : d130566 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101907, d130566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d101907, d130566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro23627 (p : Pattern) (ha : d9497 p = 1) (hb : d130577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52386 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9330 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
    | true =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
  have h3 (q : Pattern) (ha : d9331 q = 1) (hb : d100982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d9332 q = 1) (hb : d100983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9487 q = 1) (hb : d101102 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9487, d101102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9487, d101102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d9496 q = 1) (hb : d101111 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9496, d101111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9496, d101111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d9497 q = 1) (hb : d130577 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9497, d130577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9497, d130577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23628 (p : Pattern) (ha : d9556 p = 1) (hb : d130588 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9498 q = 1) (hb : d130578 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9498, d130578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23627 q ha hb
    | true =>
      simp only [d9498, d130578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9499 q = 1) (hb : d130579 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9499, d130579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9499, d130579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9553 q = 1) (hb : d130585 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9553, d130585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9553, d130585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9554 q = 1) (hb : d130586 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9554, d130586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9554, d130586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9555 q = 1) (hb : d130587 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9555, d130587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9555, d130587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9556 q = 1) (hb : d130588 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9556, d130588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9556, d130588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23629 (p : Pattern) (ha : d9562 p = 1) (hb : d130607 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9557 q = 1) (hb : d130602 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9557, d130602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23628 q ha hb
    | true =>
      simp only [d9557, d130602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9558 q = 1) (hb : d130603 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9558, d130603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9558, d130603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9559 q = 1) (hb : d130604 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9559, d130604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9559, d130604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9560 q = 1) (hb : d130605 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9560, d130605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9560, d130605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9561 q = 1) (hb : d130606 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9561, d130606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9561, d130606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9562 q = 1) (hb : d130607 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9562, d130607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9562, d130607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23630 (p : Pattern) (ha : d9484 p = 1) (hb : d130567 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127062 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9475 q = 1) (hb : d101090 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9475, d101090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23274 q ha hb
    | true =>
      simp only [d9475, d101090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23262 q ha hb
  have h3 (q : Pattern) (ha : d9476 q = 1) (hb : d101091 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9476, d101091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9476, d101091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d9477 q = 1) (hb : d101092 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9477, d101092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9477, d101092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9479 q = 1) (hb : d101094 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9479, d101094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23262 q ha hb
    | true =>
      simp only [d9479, d101094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23275 q ha hb
  have h6 (q : Pattern) (ha : d9480 q = 1) (hb : d101095 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9480, d101095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9480, d101095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d9481 q = 1) (hb : d101096 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9481, d101096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9481, d101096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9482 q = 1) (hb : d101097 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9482, d101097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9482, d101097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9389 q = 1) (hb : d101022 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23262 q ha hb
    | true =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
  have h10 (q : Pattern) (ha : d9390 q = 1) (hb : d101023 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9390, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9390, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d9391 q = 1) (hb : d101024 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9391, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9391, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9330 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
    | true =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
  have h13 (q : Pattern) (ha : d9331 q = 1) (hb : d100982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d9332 q = 1) (hb : d100983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d9392 q = 1) (hb : d101025 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9392, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9392, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9483 q = 1) (hb : d101098 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9483, d101098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9483, d101098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9484 q = 1) (hb : d130567 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9484, d130567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9484, d130567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro23631 (p : Pattern) (ha : d9489 p = 1) (hb : d130570 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127066 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9389 q = 1) (hb : d101022 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23262 q ha hb
    | true =>
      simp only [d9389, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
  have h3 (q : Pattern) (ha : d9390 q = 1) (hb : d101023 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9390, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9390, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d9391 q = 1) (hb : d101024 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9391, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9391, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9330 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23255 q ha hb
    | true =>
      simp only [d9330, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23250 q ha hb
  have h6 (q : Pattern) (ha : d9331 q = 1) (hb : d100982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9331, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d9332 q = 1) (hb : d100983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9332, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9392 q = 1) (hb : d101025 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9392, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9392, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9487 q = 1) (hb : d101102 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9487, d101102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9487, d101102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d9488 q = 1) (hb : d101103 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9488, d101103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9488, d101103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9489 q = 1) (hb : d130570 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9489, d130570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9489, d130570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro23632 (p : Pattern) (ha : d9495 p = 1) (hb : d130576 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9485 q = 1) (hb : d130568 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9485, d130568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23630 q ha hb
    | true =>
      simp only [d9485, d130568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9486 q = 1) (hb : d130569 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9486, d130569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9486, d130569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9490 q = 1) (hb : d130571 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9490, d130571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23631 q ha hb
    | true =>
      simp only [d9490, d130571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9491 q = 1) (hb : d130572 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9491, d130572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9491, d130572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9492 q = 1) (hb : d130573 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9492, d130573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9492, d130573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9493 q = 1) (hb : d130574 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9493, d130574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9493, d130574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9494 q = 1) (hb : d130575 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9494, d130575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9494, d130575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9495 q = 1) (hb : d130576 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9495, d130576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9495, d130576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23633 (p : Pattern) (ha : d9503 p = 1) (hb : d130583 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9490 q = 1) (hb : d130571 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9490, d130571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23631 q ha hb
    | true =>
      simp only [d9490, d130571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9491 q = 1) (hb : d130572 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9491, d130572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9491, d130572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9498 q = 1) (hb : d130578 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9498, d130578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23627 q ha hb
    | true =>
      simp only [d9498, d130578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9499 q = 1) (hb : d130579 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9499, d130579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9499, d130579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9500 q = 1) (hb : d130580 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9500, d130580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9500, d130580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9501 q = 1) (hb : d130581 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9501, d130581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9501, d130581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9502 q = 1) (hb : d130582 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9502, d130582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9502, d130582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9503 q = 1) (hb : d130583 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9503, d130583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9503, d130583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23634 (p : Pattern) (ha : d9545 p = 1) (hb : d130594 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9490 q = 1) (hb : d130571 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9490, d130571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23631 q ha hb
    | true =>
      simp only [d9490, d130571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9491 q = 1) (hb : d130572 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9491, d130572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9491, d130572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9542 q = 1) (hb : d130591 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9542, d130591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9542, d130591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9543 q = 1) (hb : d130592 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9543, d130592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9543, d130592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9544 q = 1) (hb : d130593 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9544, d130593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9544, d130593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9545 q = 1) (hb : d130594 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9545, d130594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9545, d130594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23635 (p : Pattern) (ha : d101912 p = 1) (hb : d130600 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9504 q = 1) (hb : d130584 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9504, d130584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23632 q ha hb
    | true =>
      simp only [d9504, d130584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23633 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130589 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101908 q = 1) (hb : d130590 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101908, d130590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101908, d130590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9546 q = 1) (hb : d130595 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9546, d130595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23634 q ha hb
    | true =>
      simp only [d9546, d130595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9547 q = 1) (hb : d130596 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9547, d130596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9547, d130596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101909 q = 1) (hb : d130597 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101909, d130597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101909, d130597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101910 q = 1) (hb : d130598 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101910, d130598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101910, d130598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101911 q = 1) (hb : d130599 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101911, d130599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101911, d130599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d101912 q = 1) (hb : d130600 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101912, d130600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101912, d130600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro23636 (p : Pattern) (ha : d101918 p = 1) (hb : d130613 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101913 q = 1) (hb : d130601 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101913, d130601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101913, d130601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23635 q ha hb
  have h2 (q : Pattern) (ha : d9563 q = 1) (hb : d130608 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9563, d130608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9563, d130608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23629 q ha hb
  have h3 (q : Pattern) (ha : d101914 q = 1) (hb : d130609 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101914, d130609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101914, d130609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101915 q = 1) (hb : d130610 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101915, d130610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101915, d130610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d101916 q = 1) (hb : d130611 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101916, d130611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101916, d130611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101917 q = 1) (hb : d130612 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101917, d130612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101917, d130612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d101918 q = 1) (hb : d130613 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101918, d130613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101918, d130613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23637 (p : Pattern) (ha : d101924 p = 1) (hb : d130619 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101919 q = 1) (hb : d130614 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101919, d130614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101919, d130614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23636 q ha hb
  have h2 (q : Pattern) (ha : d101920 q = 1) (hb : d130615 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101920, d130615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101920, d130615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101921 q = 1) (hb : d130616 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101921, d130616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101921, d130616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101922 q = 1) (hb : d130617 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101922, d130617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101922, d130617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101923 q = 1) (hb : d130618 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101923, d130618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101923, d130618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101924 q = 1) (hb : d130619 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101924, d130619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101924, d130619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23638 (p : Pattern) (ha : d9642 p = 1) (hb : d130631 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52623 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9624 q = 1) (hb : d101204 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23284 q ha hb
    | true =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23285 q ha hb
  have h3 (q : Pattern) (ha : d9625 q = 1) (hb : d101205 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9625, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9625, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d9626 q = 1) (hb : d101206 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9626, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9626, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9632 q = 1) (hb : d101212 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9632, d101212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9632, d101212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d9641 q = 1) (hb : d101221 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9641, d101221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9641, d101221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d9642 q = 1) (hb : d130631 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9642, d130631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9642, d130631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23639 (p : Pattern) (ha : d9725 p = 1) (hb : d130642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9643 q = 1) (hb : d130632 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9643, d130632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23638 q ha hb
    | true =>
      simp only [d9643, d130632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9644 q = 1) (hb : d130633 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9644, d130633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9644, d130633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9722 q = 1) (hb : d130639 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9722, d130639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9722, d130639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9723 q = 1) (hb : d130640 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9723, d130640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9723, d130640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9724 q = 1) (hb : d130641 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9724, d130641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9724, d130641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9725 q = 1) (hb : d130642 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9725, d130642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9725, d130642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23640 (p : Pattern) (ha : d9731 p = 1) (hb : d130661 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9726 q = 1) (hb : d130656 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9726, d130656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23639 q ha hb
    | true =>
      simp only [d9726, d130656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9727 q = 1) (hb : d130657 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9727, d130657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9727, d130657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9728 q = 1) (hb : d130658 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9728, d130658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9728, d130658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9729 q = 1) (hb : d130659 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9729, d130659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9729, d130659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9730 q = 1) (hb : d130660 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9730, d130660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9730, d130660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9731 q = 1) (hb : d130661 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9731, d130661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9731, d130661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23641 (p : Pattern) (ha : d9629 p = 1) (hb : d130621 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127233 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9609 q = 1) (hb : d101189 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9609, d101189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23292 q ha hb
    | true =>
      simp only [d9609, d101189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23293 q ha hb
  have h3 (q : Pattern) (ha : d9610 q = 1) (hb : d101190 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9610, d101190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9610, d101190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d9611 q = 1) (hb : d101191 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9611, d101191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9611, d101191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9614 q = 1) (hb : d101194 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9614, d101194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23293 q ha hb
    | true =>
      simp only [d9614, d101194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23294 q ha hb
  have h6 (q : Pattern) (ha : d9615 q = 1) (hb : d101195 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9615, d101195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9615, d101195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d9616 q = 1) (hb : d101196 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9616, d101196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9616, d101196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9617 q = 1) (hb : d101197 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9617, d101197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9617, d101197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9620 q = 1) (hb : d101200 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9620, d101200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23293 q ha hb
    | true =>
      simp only [d9620, d101200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23284 q ha hb
  have h10 (q : Pattern) (ha : d9621 q = 1) (hb : d101201 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9621, d101201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9621, d101201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d9622 q = 1) (hb : d101202 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9622, d101202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9622, d101202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9624 q = 1) (hb : d101204 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23284 q ha hb
    | true =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23285 q ha hb
  have h13 (q : Pattern) (ha : d9625 q = 1) (hb : d101205 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9625, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9625, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d9626 q = 1) (hb : d101206 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9626, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9626, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d9627 q = 1) (hb : d101207 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9627, d101207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9627, d101207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9628 q = 1) (hb : d101208 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9628, d101208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9628, d101208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9629 q = 1) (hb : d130621 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9629, d130621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9629, d130621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro23642 (p : Pattern) (ha : d9634 p = 1) (hb : d130624 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127237 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9620 q = 1) (hb : d101200 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9620, d101200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23293 q ha hb
    | true =>
      simp only [d9620, d101200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23284 q ha hb
  have h3 (q : Pattern) (ha : d9621 q = 1) (hb : d101201 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9621, d101201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9621, d101201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d9622 q = 1) (hb : d101202 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9622, d101202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9622, d101202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9624 q = 1) (hb : d101204 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23284 q ha hb
    | true =>
      simp only [d9624, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23285 q ha hb
  have h6 (q : Pattern) (ha : d9625 q = 1) (hb : d101205 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9625, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9625, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d9626 q = 1) (hb : d101206 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9626, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9626, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9627 q = 1) (hb : d101207 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9627, d101207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9627, d101207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9632 q = 1) (hb : d101212 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9632, d101212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9632, d101212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d9633 q = 1) (hb : d101213 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9633, d101213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9633, d101213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9634 q = 1) (hb : d130624 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9634, d130624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9634, d130624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro23643 (p : Pattern) (ha : d9640 p = 1) (hb : d130630 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9630 q = 1) (hb : d130622 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9630, d130622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23641 q ha hb
    | true =>
      simp only [d9630, d130622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9631 q = 1) (hb : d130623 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9631, d130623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9631, d130623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9635 q = 1) (hb : d130625 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9635, d130625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23642 q ha hb
    | true =>
      simp only [d9635, d130625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9636 q = 1) (hb : d130626 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9636, d130626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9636, d130626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9637 q = 1) (hb : d130627 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9637, d130627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9637, d130627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9638 q = 1) (hb : d130628 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9638, d130628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9638, d130628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9639 q = 1) (hb : d130629 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9639, d130629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9639, d130629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9640 q = 1) (hb : d130630 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9640, d130630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9640, d130630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23644 (p : Pattern) (ha : d9648 p = 1) (hb : d130637 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9635 q = 1) (hb : d130625 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9635, d130625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23642 q ha hb
    | true =>
      simp only [d9635, d130625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9636 q = 1) (hb : d130626 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9636, d130626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9636, d130626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9643 q = 1) (hb : d130632 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9643, d130632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23638 q ha hb
    | true =>
      simp only [d9643, d130632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9644 q = 1) (hb : d130633 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9644, d130633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9644, d130633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9645 q = 1) (hb : d130634 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9645, d130634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9645, d130634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9646 q = 1) (hb : d130635 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9646, d130635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9646, d130635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9647 q = 1) (hb : d130636 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9647, d130636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9647, d130636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9648 q = 1) (hb : d130637 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9648, d130637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9648, d130637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23645 (p : Pattern) (ha : d9714 p = 1) (hb : d130648 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9635 q = 1) (hb : d130625 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9635, d130625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23642 q ha hb
    | true =>
      simp only [d9635, d130625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9636 q = 1) (hb : d130626 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9636, d130626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9636, d130626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9711 q = 1) (hb : d130645 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9711, d130645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9711, d130645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9712 q = 1) (hb : d130646 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9712, d130646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9712, d130646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9713 q = 1) (hb : d130647 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9713, d130647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9713, d130647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9714 q = 1) (hb : d130648 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9714, d130648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9714, d130648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23646 (p : Pattern) (ha : d101930 p = 1) (hb : d130654 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9649 q = 1) (hb : d130638 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9649, d130638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23643 q ha hb
    | true =>
      simp only [d9649, d130638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23644 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130643 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101926 q = 1) (hb : d130644 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101926, d130644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101926, d130644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9715 q = 1) (hb : d130649 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9715, d130649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23645 q ha hb
    | true =>
      simp only [d9715, d130649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9716 q = 1) (hb : d130650 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9716, d130650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9716, d130650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101927 q = 1) (hb : d130651 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101927, d130651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101927, d130651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101928 q = 1) (hb : d130652 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101928, d130652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101928, d130652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101929 q = 1) (hb : d130653 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101929, d130653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101929, d130653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d101930 q = 1) (hb : d130654 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101930, d130654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101930, d130654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro23647 (p : Pattern) (ha : d101936 p = 1) (hb : d130667 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101931 q = 1) (hb : d130655 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101931, d130655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101931, d130655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23646 q ha hb
  have h2 (q : Pattern) (ha : d9732 q = 1) (hb : d130662 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9732, d130662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9732, d130662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23640 q ha hb
  have h3 (q : Pattern) (ha : d101932 q = 1) (hb : d130663 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101932, d130663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101932, d130663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101933 q = 1) (hb : d130664 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101933, d130664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101933, d130664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d101934 q = 1) (hb : d130665 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101934, d130665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101934, d130665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101935 q = 1) (hb : d130666 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101935, d130666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101935, d130666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d101936 q = 1) (hb : d130667 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101936, d130667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101936, d130667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23648 (p : Pattern) (ha : d101942 p = 1) (hb : d130673 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101937 q = 1) (hb : d130668 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101937, d130668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101937, d130668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23647 q ha hb
  have h2 (q : Pattern) (ha : d101938 q = 1) (hb : d130669 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101938, d130669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101938, d130669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101939 q = 1) (hb : d130670 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101939, d130670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101939, d130670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101940 q = 1) (hb : d130671 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101940, d130671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101940, d130671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101941 q = 1) (hb : d130672 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101941, d130672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101941, d130672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101942 q = 1) (hb : d130673 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101942, d130673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101942, d130673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23649 (p : Pattern) (ha : d9875 p = 1) (hb : d130686 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127498 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9870 q = 1) (hb : d101391 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9870, d101391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9870, d101391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23306 q ha hb
  have h3 (q : Pattern) (ha : d9871 q = 1) (hb : d101392 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9871, d101392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9871, d101392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d9872 q = 1) (hb : d101393 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9872, d101393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9872, d101393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9873 q = 1) (hb : d101394 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9873, d101394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9873, d101394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d9874 q = 1) (hb : d101395 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9874, d101395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9874, d101395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d9875 q = 1) (hb : d130686 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9875, d130686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9875, d130686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23650 (p : Pattern) (ha : d10010 p = 1) (hb : d130704 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9876 q = 1) (hb : d130687 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9876, d130687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23649 q ha hb
    | true =>
      simp only [d9876, d130687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9877 q = 1) (hb : d130688 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9877, d130688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9877, d130688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10007 q = 1) (hb : d130701 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10007, d130701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10007, d130701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10008 q = 1) (hb : d130702 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10008, d130702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10008, d130702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10009 q = 1) (hb : d130703 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10009, d130703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10009, d130703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10010 q = 1) (hb : d130704 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10010, d130704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10010, d130704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23651 (p : Pattern) (ha : d10016 p = 1) (hb : d130726 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10011 q = 1) (hb : d130721 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10011, d130721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23650 q ha hb
    | true =>
      simp only [d10011, d130721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10012 q = 1) (hb : d130722 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10012, d130722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10012, d130722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10013 q = 1) (hb : d130723 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10013, d130723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10013, d130723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10014 q = 1) (hb : d130724 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10014, d130724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10014, d130724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10015 q = 1) (hb : d130725 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10015, d130725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10015, d130725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10016 q = 1) (hb : d130726 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10016, d130726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10016, d130726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23652 (p : Pattern) (ha : d9856 p = 1) (hb : d130676 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127481 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9807 q = 1) (hb : d101328 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9807, d101328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23314 q ha hb
    | true =>
      simp only [d9807, d101328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23316 q ha hb
  have h3 (q : Pattern) (ha : d9808 q = 1) (hb : d101329 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9808, d101329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9808, d101329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d9809 q = 1) (hb : d101330 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9809, d101330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9809, d101330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9822 q = 1) (hb : d101343 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9822, d101343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23316 q ha hb
    | true =>
      simp only [d9822, d101343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23318 q ha hb
  have h6 (q : Pattern) (ha : d9823 q = 1) (hb : d101344 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9823, d101344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9823, d101344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d9824 q = 1) (hb : d101345 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9824, d101345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9824, d101345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9825 q = 1) (hb : d101346 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9825, d101346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9825, d101346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9834 q = 1) (hb : d101355 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23316 q ha hb
    | true =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
  have h10 (q : Pattern) (ha : d9835 q = 1) (hb : d101356 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d9836 q = 1) (hb : d101357 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9851 q = 1) (hb : d101372 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23319 q ha hb
  have h13 (q : Pattern) (ha : d9852 q = 1) (hb : d101373 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d9853 q = 1) (hb : d101374 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d9854 q = 1) (hb : d101375 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d9855 q = 1) (hb : d101376 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9855, d101376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9855, d101376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9856 q = 1) (hb : d130676 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9856, d130676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9856, d130676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro23653 (p : Pattern) (ha : d9861 p = 1) (hb : d130679 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127486 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9834 q = 1) (hb : d101355 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23316 q ha hb
    | true =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
  have h3 (q : Pattern) (ha : d9835 q = 1) (hb : d101356 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d9836 q = 1) (hb : d101357 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9851 q = 1) (hb : d101372 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23319 q ha hb
  have h6 (q : Pattern) (ha : d9852 q = 1) (hb : d101373 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d9853 q = 1) (hb : d101374 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9854 q = 1) (hb : d101375 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9859 q = 1) (hb : d101380 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9859, d101380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9859, d101380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d9860 q = 1) (hb : d101381 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9860, d101381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9860, d101381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9861 q = 1) (hb : d130679 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9861, d130679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9861, d130679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro23654 (p : Pattern) (ha : d9867 p = 1) (hb : d130685 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9857 q = 1) (hb : d130677 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9857, d130677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23652 q ha hb
    | true =>
      simp only [d9857, d130677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9858 q = 1) (hb : d130678 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9858, d130678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9858, d130678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9862 q = 1) (hb : d130680 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9862, d130680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23653 q ha hb
    | true =>
      simp only [d9862, d130680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9863 q = 1) (hb : d130681 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9863, d130681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9863, d130681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9864 q = 1) (hb : d130682 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9864, d130682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9864, d130682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9865 q = 1) (hb : d130683 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9865, d130683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9865, d130683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9866 q = 1) (hb : d130684 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9866, d130684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9866, d130684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9867 q = 1) (hb : d130685 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9867, d130685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9867, d130685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23655 (p : Pattern) (ha : d9881 p = 1) (hb : d130692 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9862 q = 1) (hb : d130680 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9862, d130680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23653 q ha hb
    | true =>
      simp only [d9862, d130680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9863 q = 1) (hb : d130681 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9863, d130681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9863, d130681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9876 q = 1) (hb : d130687 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9876, d130687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23649 q ha hb
    | true =>
      simp only [d9876, d130687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9877 q = 1) (hb : d130688 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9877, d130688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9877, d130688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9878 q = 1) (hb : d130689 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9878, d130689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9878, d130689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9879 q = 1) (hb : d130690 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9879, d130690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9879, d130690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9880 q = 1) (hb : d130691 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9880, d130691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9880, d130691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d9881 q = 1) (hb : d130692 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9881, d130692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9881, d130692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23656 (p : Pattern) (ha : d9993 p = 1) (hb : d130707 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127525 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9834 q = 1) (hb : d101355 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23316 q ha hb
    | true =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
  have h3 (q : Pattern) (ha : d9835 q = 1) (hb : d101356 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d9836 q = 1) (hb : d101357 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9851 q = 1) (hb : d101372 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23319 q ha hb
  have h6 (q : Pattern) (ha : d9852 q = 1) (hb : d101373 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d9853 q = 1) (hb : d101374 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9854 q = 1) (hb : d101375 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9988 q = 1) (hb : d101419 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9988, d101419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9988, d101419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23324 q ha hb
  have h10 (q : Pattern) (ha : d9989 q = 1) (hb : d101420 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9989, d101420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9989, d101420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d9990 q = 1) (hb : d101421 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9990, d101421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9990, d101421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9991 q = 1) (hb : d101422 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9991, d101422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9991, d101422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d9992 q = 1) (hb : d101423 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d9992, d101423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9992, d101423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d9993 q = 1) (hb : d130707 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d9993, d130707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9993, d130707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro23657 (p : Pattern) (ha : d9999 p = 1) (hb : d130713 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9994 q = 1) (hb : d130708 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9994, d130708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23656 q ha hb
    | true =>
      simp only [d9994, d130708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9995 q = 1) (hb : d130709 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9995, d130709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9995, d130709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9996 q = 1) (hb : d130710 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d9996, d130710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9996, d130710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9997 q = 1) (hb : d130711 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d9997, d130711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9997, d130711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9998 q = 1) (hb : d130712 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d9998, d130712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9998, d130712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9999 q = 1) (hb : d130713 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d9999, d130713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9999, d130713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23658 (p : Pattern) (ha : d101949 p = 1) (hb : d130719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9882 q = 1) (hb : d130693 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9882, d130693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23654 q ha hb
    | true =>
      simp only [d9882, d130693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23655 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130705 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101945 q = 1) (hb : d130706 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101945, d130706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101945, d130706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10000 q = 1) (hb : d130714 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10000, d130714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23657 q ha hb
    | true =>
      simp only [d10000, d130714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10001 q = 1) (hb : d130715 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10001, d130715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10001, d130715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101946 q = 1) (hb : d130716 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101946, d130716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101946, d130716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101947 q = 1) (hb : d130717 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101947, d130717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101947, d130717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101948 q = 1) (hb : d130718 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101948, d130718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101948, d130718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d101949 q = 1) (hb : d130719 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101949, d130719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101949, d130719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro23659 (p : Pattern) (ha : d101955 p = 1) (hb : d130732 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101950 q = 1) (hb : d130720 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101950, d130720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101950, d130720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23658 q ha hb
  have h2 (q : Pattern) (ha : d10017 q = 1) (hb : d130727 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10017, d130727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10017, d130727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23651 q ha hb
  have h3 (q : Pattern) (ha : d101951 q = 1) (hb : d130728 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101951, d130728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101951, d130728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101952 q = 1) (hb : d130729 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101952, d130729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101952, d130729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d101953 q = 1) (hb : d130730 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101953, d130730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101953, d130730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101954 q = 1) (hb : d130731 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101954, d130731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101954, d130731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d101955 q = 1) (hb : d130732 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101955, d130732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101955, d130732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23660 (p : Pattern) (ha : d101961 p = 1) (hb : d130738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101956 q = 1) (hb : d130733 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101956, d130733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101956, d130733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23659 q ha hb
  have h2 (q : Pattern) (ha : d101957 q = 1) (hb : d130734 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101957, d130734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101957, d130734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101958 q = 1) (hb : d130735 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101958, d130735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101958, d130735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101959 q = 1) (hb : d130736 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101959, d130736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101959, d130736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101960 q = 1) (hb : d130737 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101960, d130737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101960, d130737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101961 q = 1) (hb : d130738 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101961, d130738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101961, d130738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23661 (p : Pattern) (ha : d10169 p = 1) (hb : d130752 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127791 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10164 q = 1) (hb : d101591 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10164, d101591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10164, d101591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23334 q ha hb
  have h3 (q : Pattern) (ha : d10165 q = 1) (hb : d101592 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10165, d101592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10165, d101592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d10166 q = 1) (hb : d101593 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10166, d101593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10166, d101593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10167 q = 1) (hb : d101594 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10167, d101594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10167, d101594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d10168 q = 1) (hb : d101595 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10168, d101595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10168, d101595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d10169 q = 1) (hb : d130752 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10169, d130752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10169, d130752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23662 (p : Pattern) (ha : d10316 p = 1) (hb : d130770 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10170 q = 1) (hb : d130753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10170, d130753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23661 q ha hb
    | true =>
      simp only [d10170, d130753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10171 q = 1) (hb : d130754 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10171, d130754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10171, d130754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10313 q = 1) (hb : d130767 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10313, d130767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10313, d130767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10314 q = 1) (hb : d130768 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10314, d130768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10314, d130768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10315 q = 1) (hb : d130769 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10315, d130769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10315, d130769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10316 q = 1) (hb : d130770 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10316, d130770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10316, d130770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23663 (p : Pattern) (ha : d10322 p = 1) (hb : d130792 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10317 q = 1) (hb : d130787 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10317, d130787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23662 q ha hb
    | true =>
      simp only [d10317, d130787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10318 q = 1) (hb : d130788 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10318, d130788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10318, d130788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10319 q = 1) (hb : d130789 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10319, d130789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10319, d130789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10320 q = 1) (hb : d130790 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10320, d130790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10320, d130790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10321 q = 1) (hb : d130791 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10321, d130791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10321, d130791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10322 q = 1) (hb : d130792 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10322, d130792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10322, d130792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23664 (p : Pattern) (ha : d10147 p = 1) (hb : d130742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127774 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10092 q = 1) (hb : d101519 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10092, d101519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23342 q ha hb
    | true =>
      simp only [d10092, d101519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23344 q ha hb
  have h3 (q : Pattern) (ha : d10093 q = 1) (hb : d101520 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10093, d101520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10093, d101520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d10094 q = 1) (hb : d101521 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10094, d101521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10094, d101521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10107 q = 1) (hb : d101534 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10107, d101534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23344 q ha hb
    | true =>
      simp only [d10107, d101534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23346 q ha hb
  have h6 (q : Pattern) (ha : d10108 q = 1) (hb : d101535 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10108, d101535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10108, d101535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d10109 q = 1) (hb : d101536 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10109, d101536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10109, d101536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10110 q = 1) (hb : d101537 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10110, d101537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10110, d101537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10122 q = 1) (hb : d101549 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23344 q ha hb
    | true =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
  have h10 (q : Pattern) (ha : d10123 q = 1) (hb : d101550 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d10124 q = 1) (hb : d101551 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10142 q = 1) (hb : d101569 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23347 q ha hb
  have h13 (q : Pattern) (ha : d10143 q = 1) (hb : d101570 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d10144 q = 1) (hb : d101571 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d10145 q = 1) (hb : d101572 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10146 q = 1) (hb : d101573 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10146, d101573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10146, d101573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10147 q = 1) (hb : d130742 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10147, d130742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10147, d130742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro23665 (p : Pattern) (ha : d10152 p = 1) (hb : d130745 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127779 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10122 q = 1) (hb : d101549 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23344 q ha hb
    | true =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
  have h3 (q : Pattern) (ha : d10123 q = 1) (hb : d101550 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d10124 q = 1) (hb : d101551 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10142 q = 1) (hb : d101569 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23347 q ha hb
  have h6 (q : Pattern) (ha : d10143 q = 1) (hb : d101570 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d10144 q = 1) (hb : d101571 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10145 q = 1) (hb : d101572 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10150 q = 1) (hb : d101577 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10150, d101577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10150, d101577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d10151 q = 1) (hb : d101578 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10151, d101578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10151, d101578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10152 q = 1) (hb : d130745 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10152, d130745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10152, d130745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro23666 (p : Pattern) (ha : d10158 p = 1) (hb : d130751 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10148 q = 1) (hb : d130743 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10148, d130743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23664 q ha hb
    | true =>
      simp only [d10148, d130743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10149 q = 1) (hb : d130744 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10149, d130744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10149, d130744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10153 q = 1) (hb : d130746 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10153, d130746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23665 q ha hb
    | true =>
      simp only [d10153, d130746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10154 q = 1) (hb : d130747 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10154, d130747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10154, d130747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10155 q = 1) (hb : d130748 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10155, d130748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10155, d130748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10156 q = 1) (hb : d130749 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10156, d130749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10156, d130749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10157 q = 1) (hb : d130750 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10157, d130750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10157, d130750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10158 q = 1) (hb : d130751 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10158, d130751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10158, d130751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23667 (p : Pattern) (ha : d10175 p = 1) (hb : d130758 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10153 q = 1) (hb : d130746 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10153, d130746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23665 q ha hb
    | true =>
      simp only [d10153, d130746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10154 q = 1) (hb : d130747 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10154, d130747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10154, d130747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10170 q = 1) (hb : d130753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10170, d130753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23661 q ha hb
    | true =>
      simp only [d10170, d130753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10171 q = 1) (hb : d130754 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10171, d130754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10171, d130754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10172 q = 1) (hb : d130755 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10172, d130755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10172, d130755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10173 q = 1) (hb : d130756 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10173, d130756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10173, d130756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10174 q = 1) (hb : d130757 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10174, d130757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10174, d130757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10175 q = 1) (hb : d130758 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10175, d130758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10175, d130758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23668 (p : Pattern) (ha : d10299 p = 1) (hb : d130773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127818 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10122 q = 1) (hb : d101549 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23344 q ha hb
    | true =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
  have h3 (q : Pattern) (ha : d10123 q = 1) (hb : d101550 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d10124 q = 1) (hb : d101551 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10142 q = 1) (hb : d101569 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23347 q ha hb
  have h6 (q : Pattern) (ha : d10143 q = 1) (hb : d101570 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d10144 q = 1) (hb : d101571 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10145 q = 1) (hb : d101572 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10294 q = 1) (hb : d101619 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10294, d101619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10294, d101619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23352 q ha hb
  have h10 (q : Pattern) (ha : d10295 q = 1) (hb : d101620 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10295, d101620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10295, d101620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d10296 q = 1) (hb : d101621 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10296, d101621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10296, d101621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10297 q = 1) (hb : d101622 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10297, d101622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10297, d101622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d10298 q = 1) (hb : d101623 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10298, d101623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10298, d101623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10299 q = 1) (hb : d130773 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10299, d130773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10299, d130773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro23669 (p : Pattern) (ha : d10305 p = 1) (hb : d130779 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10300 q = 1) (hb : d130774 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10300, d130774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23668 q ha hb
    | true =>
      simp only [d10300, d130774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10301 q = 1) (hb : d130775 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10301, d130775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10301, d130775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10302 q = 1) (hb : d130776 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10302, d130776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10302, d130776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10303 q = 1) (hb : d130777 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10303, d130777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10303, d130777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10304 q = 1) (hb : d130778 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10304, d130778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10304, d130778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10305 q = 1) (hb : d130779 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10305, d130779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10305, d130779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23670 (p : Pattern) (ha : d101969 p = 1) (hb : d130785 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10176 q = 1) (hb : d130759 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10176, d130759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23666 q ha hb
    | true =>
      simp only [d10176, d130759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23667 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130771 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101965 q = 1) (hb : d130772 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101965, d130772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101965, d130772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10306 q = 1) (hb : d130780 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10306, d130780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23669 q ha hb
    | true =>
      simp only [d10306, d130780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10307 q = 1) (hb : d130781 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10307, d130781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10307, d130781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101966 q = 1) (hb : d130782 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101966, d130782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101966, d130782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101967 q = 1) (hb : d130783 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101967, d130783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101967, d130783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101968 q = 1) (hb : d130784 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101968, d130784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101968, d130784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d101969 q = 1) (hb : d130785 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101969, d130785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101969, d130785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro23671 (p : Pattern) (ha : d101975 p = 1) (hb : d130798 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101970 q = 1) (hb : d130786 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101970, d130786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101970, d130786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23670 q ha hb
  have h2 (q : Pattern) (ha : d10323 q = 1) (hb : d130793 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10323, d130793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10323, d130793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23663 q ha hb
  have h3 (q : Pattern) (ha : d101971 q = 1) (hb : d130794 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101971, d130794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101971, d130794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101972 q = 1) (hb : d130795 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101972, d130795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101972, d130795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d101973 q = 1) (hb : d130796 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101973, d130796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101973, d130796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101974 q = 1) (hb : d130797 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101974, d130797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101974, d130797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d101975 q = 1) (hb : d130798 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101975, d130798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101975, d130798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23672 (p : Pattern) (ha : d101981 p = 1) (hb : d130804 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101976 q = 1) (hb : d130799 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101976, d130799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101976, d130799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23671 q ha hb
  have h2 (q : Pattern) (ha : d101977 q = 1) (hb : d130800 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101977, d130800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101977, d130800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101978 q = 1) (hb : d130801 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101978, d130801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101978, d130801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101979 q = 1) (hb : d130802 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d101979, d130802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101979, d130802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d101980 q = 1) (hb : d130803 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d101980, d130803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101980, d130803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101981 q = 1) (hb : d130804 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d101981, d130804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101981, d130804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23673 (p : Pattern) (ha : d10446 p = 1) (hb : d130819 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128083 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10441 q = 1) (hb : d101762 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10441, d101762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10441, d101762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23362 q ha hb
  have h3 (q : Pattern) (ha : d10442 q = 1) (hb : d101763 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10442, d101763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10442, d101763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d10443 q = 1) (hb : d101764 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10443, d101764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10443, d101764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10444 q = 1) (hb : d101765 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10444, d101765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10444, d101765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d10445 q = 1) (hb : d101766 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10445, d101766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10445, d101766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d10446 q = 1) (hb : d130819 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10446, d130819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10446, d130819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23674 (p : Pattern) (ha : d10582 p = 1) (hb : d130837 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10447 q = 1) (hb : d130820 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10447, d130820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23673 q ha hb
    | true =>
      simp only [d10447, d130820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10448 q = 1) (hb : d130821 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10448, d130821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10448, d130821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10579 q = 1) (hb : d130834 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10579, d130834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10579, d130834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10580 q = 1) (hb : d130835 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10580, d130835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10580, d130835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10581 q = 1) (hb : d130836 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10581, d130836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10581, d130836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10582 q = 1) (hb : d130837 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10582, d130837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10582, d130837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23675 (p : Pattern) (ha : d10588 p = 1) (hb : d130859 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10583 q = 1) (hb : d130854 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10583, d130854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23674 q ha hb
    | true =>
      simp only [d10583, d130854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10584 q = 1) (hb : d130855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10584, d130855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10584, d130855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10585 q = 1) (hb : d130856 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10585, d130856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10585, d130856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10586 q = 1) (hb : d130857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10586, d130857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10586, d130857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10587 q = 1) (hb : d130858 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10587, d130858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10587, d130858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10588 q = 1) (hb : d130859 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10588, d130859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10588, d130859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23676 (p : Pattern) (ha : d10424 p = 1) (hb : d130809 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128066 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10378 q = 1) (hb : d101699 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10378, d101699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23368 q ha hb
    | true =>
      simp only [d10378, d101699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23370 q ha hb
  have h3 (q : Pattern) (ha : d10379 q = 1) (hb : d101700 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10379, d101700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10379, d101700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d10380 q = 1) (hb : d101701 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10380, d101701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10380, d101701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10383 q = 1) (hb : d101704 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10383, d101704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23370 q ha hb
    | true =>
      simp only [d10383, d101704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23371 q ha hb
  have h6 (q : Pattern) (ha : d10384 q = 1) (hb : d101705 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10384, d101705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10384, d101705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d10385 q = 1) (hb : d101706 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10385, d101706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10385, d101706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10386 q = 1) (hb : d101707 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10386, d101707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10386, d101707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10398 q = 1) (hb : d101719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23370 q ha hb
    | true =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
  have h10 (q : Pattern) (ha : d10399 q = 1) (hb : d101720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d10400 q = 1) (hb : d101721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10419 q = 1) (hb : d101740 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23372 q ha hb
  have h13 (q : Pattern) (ha : d10420 q = 1) (hb : d101741 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h14 (q : Pattern) (ha : d10421 q = 1) (hb : d101742 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d10422 q = 1) (hb : d101743 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10423 q = 1) (hb : d101744 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10423, d101744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10423, d101744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d10424 q = 1) (hb : d130809 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10424, d130809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10424, d130809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro23677 (p : Pattern) (ha : d10429 p = 1) (hb : d130812 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128071 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10398 q = 1) (hb : d101719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23370 q ha hb
    | true =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
  have h3 (q : Pattern) (ha : d10399 q = 1) (hb : d101720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d10400 q = 1) (hb : d101721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10419 q = 1) (hb : d101740 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23372 q ha hb
  have h6 (q : Pattern) (ha : d10420 q = 1) (hb : d101741 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d10421 q = 1) (hb : d101742 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10422 q = 1) (hb : d101743 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10427 q = 1) (hb : d101748 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10427, d101748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10427, d101748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d10428 q = 1) (hb : d101749 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10428, d101749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10428, d101749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10429 q = 1) (hb : d130812 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10429, d130812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10429, d130812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro23678 (p : Pattern) (ha : d10435 p = 1) (hb : d130818 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10425 q = 1) (hb : d130810 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10425, d130810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23676 q ha hb
    | true =>
      simp only [d10425, d130810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10426 q = 1) (hb : d130811 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10426, d130811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10426, d130811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10430 q = 1) (hb : d130813 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10430, d130813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23677 q ha hb
    | true =>
      simp only [d10430, d130813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10431 q = 1) (hb : d130814 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10431, d130814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10431, d130814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10432 q = 1) (hb : d130815 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10432, d130815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10432, d130815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10433 q = 1) (hb : d130816 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10433, d130816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10433, d130816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10434 q = 1) (hb : d130817 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10434, d130817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10434, d130817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10435 q = 1) (hb : d130818 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10435, d130818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10435, d130818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23679 (p : Pattern) (ha : d10452 p = 1) (hb : d130825 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10430 q = 1) (hb : d130813 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10430, d130813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23677 q ha hb
    | true =>
      simp only [d10430, d130813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10431 q = 1) (hb : d130814 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10431, d130814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10431, d130814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10447 q = 1) (hb : d130820 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10447, d130820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23673 q ha hb
    | true =>
      simp only [d10447, d130820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10448 q = 1) (hb : d130821 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10448, d130821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10448, d130821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10449 q = 1) (hb : d130822 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10449, d130822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10449, d130822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10450 q = 1) (hb : d130823 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10450, d130823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10450, d130823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10451 q = 1) (hb : d130824 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10451, d130824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10451, d130824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10452 q = 1) (hb : d130825 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10452, d130825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10452, d130825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23680 (p : Pattern) (ha : d10565 p = 1) (hb : d130840 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128110 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10398 q = 1) (hb : d101719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23370 q ha hb
    | true =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
  have h3 (q : Pattern) (ha : d10399 q = 1) (hb : d101720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d10400 q = 1) (hb : d101721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10419 q = 1) (hb : d101740 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23372 q ha hb
  have h6 (q : Pattern) (ha : d10420 q = 1) (hb : d101741 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d10421 q = 1) (hb : d101742 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10422 q = 1) (hb : d101743 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10560 q = 1) (hb : d101790 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10560, d101790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10560, d101790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23377 q ha hb
  have h10 (q : Pattern) (ha : d10561 q = 1) (hb : d101791 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10561, d101791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10561, d101791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d10562 q = 1) (hb : d101792 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10562, d101792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10562, d101792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10563 q = 1) (hb : d101793 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10563, d101793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10563, d101793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d10564 q = 1) (hb : d101794 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10564, d101794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10564, d101794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d10565 q = 1) (hb : d130840 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10565, d130840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10565, d130840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro23681 (p : Pattern) (ha : d10571 p = 1) (hb : d130846 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10566 q = 1) (hb : d130841 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10566, d130841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23680 q ha hb
    | true =>
      simp only [d10566, d130841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10567 q = 1) (hb : d130842 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10567, d130842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10567, d130842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10568 q = 1) (hb : d130843 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10568, d130843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10568, d130843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10569 q = 1) (hb : d130844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10569, d130844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10569, d130844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10570 q = 1) (hb : d130845 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10570, d130845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10570, d130845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10571 q = 1) (hb : d130846 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10571, d130846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10571, d130846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23682 (p : Pattern) (ha : d101990 p = 1) (hb : d130852 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10453 q = 1) (hb : d130826 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10453, d130826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23678 q ha hb
    | true =>
      simp only [d10453, d130826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23679 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130838 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d101986 q = 1) (hb : d130839 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d101986, d130839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101986, d130839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10572 q = 1) (hb : d130847 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10572, d130847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23681 q ha hb
    | true =>
      simp only [d10572, d130847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10573 q = 1) (hb : d130848 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10573, d130848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10573, d130848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101987 q = 1) (hb : d130849 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101987, d130849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101987, d130849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101988 q = 1) (hb : d130850 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d101988, d130850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101988, d130850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101989 q = 1) (hb : d130851 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d101989, d130851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101989, d130851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d101990 q = 1) (hb : d130852 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d101990, d130852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101990, d130852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro23683 (p : Pattern) (ha : d101996 p = 1) (hb : d130865 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101991 q = 1) (hb : d130853 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d101991, d130853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101991, d130853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23682 q ha hb
  have h2 (q : Pattern) (ha : d10589 q = 1) (hb : d130860 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10589, d130860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10589, d130860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23675 q ha hb
  have h3 (q : Pattern) (ha : d101992 q = 1) (hb : d130861 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d101992, d130861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101992, d130861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101993 q = 1) (hb : d130862 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d101993, d130862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101993, d130862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d101994 q = 1) (hb : d130863 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d101994, d130863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d101994, d130863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d101995 q = 1) (hb : d130864 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d101995, d130864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d101995, d130864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d101996 q = 1) (hb : d130865 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d101996, d130865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101996, d130865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23684 (p : Pattern) (ha : d102002 p = 1) (hb : d130871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d101997 q = 1) (hb : d130866 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d101997, d130866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101997, d130866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23683 q ha hb
  have h2 (q : Pattern) (ha : d101998 q = 1) (hb : d130867 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d101998, d130867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101998, d130867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d101999 q = 1) (hb : d130868 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d101999, d130868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101999, d130868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d102000 q = 1) (hb : d130869 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d102000, d130869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102000, d130869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d102001 q = 1) (hb : d130870 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d102001, d130870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102001, d130870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d102002 q = 1) (hb : d130871 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d102002, d130871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102002, d130871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23685 (p : Pattern) (ha : d102008 p = 1) (hb : d130877 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d101925 q = 1) (hb : d130620 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101925, d130620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23626 q ha hb
    | true =>
      simp only [d101925, d130620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23637 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d101943 q = 1) (hb : d130674 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101943, d130674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101943, d130674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23648 q ha hb
  have h3 (q : Pattern) (ha : d101944 q = 1) (hb : d130675 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d101944, d130675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d101944, d130675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d101962 q = 1) (hb : d130739 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101962, d130739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101962, d130739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23660 q ha hb
  have h5 (q : Pattern) (ha : d101963 q = 1) (hb : d130740 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d101963, d130740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101963, d130740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d101964 q = 1) (hb : d130741 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d101964, d130741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d101964, d130741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d101982 q = 1) (hb : d130805 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d101982, d130805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101982, d130805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23672 q ha hb
  have h8 (q : Pattern) (ha : d101983 q = 1) (hb : d130806 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d101983, d130806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101983, d130806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d101984 q = 1) (hb : d130807 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d101984, d130807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d101984, d130807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d101985 q = 1) (hb : d130808 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d101985, d130808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d101985, d130808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d102003 q = 1) (hb : d130872 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d102003, d130872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102003, d130872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23684 q ha hb
  have h12 (q : Pattern) (ha : d102004 q = 1) (hb : d130873 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d102004, d130873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102004, d130873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d102005 q = 1) (hb : d130874 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d102005, d130874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102005, d130874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d102006 q = 1) (hb : d130875 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d102006, d130875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102006, d130875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d102007 q = 1) (hb : d130876 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d102007, d130876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d102007, d130876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d102008 q = 1) (hb : d130877 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d102008, d130877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d102008, d130877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro23686 (p : Pattern) (ha : d102014 p = 1) (hb : d130883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102009 q = 1) (hb : d130878 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d102009, d130878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23685 q ha hb
    | true =>
      simp only [d102009, d130878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d102010 q = 1) (hb : d130879 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d102010, d130879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102010, d130879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d102011 q = 1) (hb : d130880 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d102011, d130880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102011, d130880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102012 q = 1) (hb : d130881 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d102012, d130881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102012, d130881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102013 q = 1) (hb : d130882 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d102013, d130882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102013, d130882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d102014 q = 1) (hb : d130883 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d102014, d130883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102014, d130883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23687 (p : Pattern) (ha : d102020 p = 1) (hb : d130889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102015 q = 1) (hb : d130884 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d102015, d130884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23686 q ha hb
    | true =>
      simp only [d102015, d130884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d102016 q = 1) (hb : d130885 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d102016, d130885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102016, d130885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d102017 q = 1) (hb : d130886 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d102017, d130886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102017, d130886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102018 q = 1) (hb : d130887 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d102018, d130887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102018, d130887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102019 q = 1) (hb : d130888 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d102019, d130888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102019, d130888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d102020 q = 1) (hb : d130889 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d102020, d130889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102020, d130889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23688 (p : Pattern) (ha : d102026 p = 1) (hb : d130895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102021 q = 1) (hb : d130890 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d102021, d130890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23687 q ha hb
    | true =>
      simp only [d102021, d130890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d102022 q = 1) (hb : d130891 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d102022, d130891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102022, d130891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d102023 q = 1) (hb : d130892 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d102023, d130892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102023, d130892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102024 q = 1) (hb : d130893 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d102024, d130893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102024, d130893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102025 q = 1) (hb : d130894 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d102025, d130894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102025, d130894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d102026 q = 1) (hb : d130895 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d102026, d130895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102026, d130895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23689 (p : Pattern) (ha : d102032 p = 1) (hb : d130901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102027 q = 1) (hb : d130896 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d102027, d130896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23688 q ha hb
    | true =>
      simp only [d102027, d130896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d102028 q = 1) (hb : d130897 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d102028, d130897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102028, d130897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d102029 q = 1) (hb : d130898 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d102029, d130898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102029, d130898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102030 q = 1) (hb : d130899 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d102030, d130899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102030, d130899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102031 q = 1) (hb : d130900 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d102031, d130900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102031, d130900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d102032 q = 1) (hb : d130901 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d102032, d130901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102032, d130901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23690 (p : Pattern) (ha : d102038 p = 1) (hb : d130907 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102033 q = 1) (hb : d130902 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d102033, d130902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23689 q ha hb
    | true =>
      simp only [d102033, d130902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d102034 q = 1) (hb : d130903 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d102034, d130903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102034, d130903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d102035 q = 1) (hb : d130904 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d102035, d130904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102035, d130904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102036 q = 1) (hb : d130905 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d102036, d130905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102036, d130905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102037 q = 1) (hb : d130906 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d102037, d130906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102037, d130906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d102038 q = 1) (hb : d130907 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d102038, d130907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102038, d130907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23691 (p : Pattern) (ha : d102044 p = 1) (hb : d130913 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102039 q = 1) (hb : d130908 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d102039, d130908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23690 q ha hb
    | true =>
      simp only [d102039, d130908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d102040 q = 1) (hb : d130909 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d102040, d130909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102040, d130909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d102041 q = 1) (hb : d130910 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d102041, d130910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102041, d130910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102042 q = 1) (hb : d130911 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d102042, d130911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102042, d130911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102043 q = 1) (hb : d130912 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d102043, d130912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102043, d130912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d102044 q = 1) (hb : d130913 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d102044, d130913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102044, d130913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23692 (p : Pattern) (ha : d102050 p = 1) (hb : d130919 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d102045 q = 1) (hb : d130914 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d102045, d130914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23691 q ha hb
    | true =>
      simp only [d102045, d130914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d102046 q = 1) (hb : d130915 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d102046, d130915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d102046, d130915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d102047 q = 1) (hb : d130916 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d102047, d130916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d102047, d130916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d102048 q = 1) (hb : d130917 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d102048, d130917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d102048, d130917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d102049 q = 1) (hb : d130918 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d102049, d130918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d102049, d130918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d102050 q = 1) (hb : d130919 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d102050, d130919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d102050, d130919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23693 (p : Pattern) (ha : d129671 p = 1) (hb : d130482 p = 1) : d129671 p = 1 := by
  have h0 (q : Pattern) (ha : d129671 q = 1) (hb : d130482 q = 1) : d129671 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro23694 (p : Pattern) (ha : d9436 p = 1) (hb : d130518 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d130513 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9309 q = 1) (hb : d130490 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9309, d130490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23613 q ha hb
    | true =>
      simp only [d9309, d130490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9432 q = 1) (hb : d130514 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9432, d130514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9432, d130514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d130491 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d9433 q = 1) (hb : d130515 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9433, d130515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9433, d130515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9434 q = 1) (hb : d130516 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9434, d130516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9434, d130516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9435 q = 1) (hb : d130517 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9435, d130517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9435, d130517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9436 q = 1) (hb : d130518 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9436, d130518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9436, d130518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23695 (p : Pattern) (ha : d129477 p = 1) (hb : d130524 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9437 q = 1) (hb : d130519 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9437, d130519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9437, d130519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23694 q ha hb
  have h2 (q : Pattern) (ha : d129473 q = 1) (hb : d130520 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129473, d130520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129473, d130520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129474 q = 1) (hb : d130521 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129474, d130521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129474, d130521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129475 q = 1) (hb : d130522 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129475, d130522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129475, d130522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129476 q = 1) (hb : d130523 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129476, d130523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129476, d130523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129477 q = 1) (hb : d130524 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129477, d130524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129477, d130524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23696 (p : Pattern) (ha : d129487 p = 1) (hb : d130548 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d130537 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9342 q = 1) (hb : d130513 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d9342, d130513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23617 q ha hb
    | true =>
      simp only [d9342, d130513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23613 q ha hb
  have h3 (q : Pattern) (ha : d129483 q = 1) (hb : d130538 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129483, d130538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129483, d130538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d130544 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d129484 q = 1) (hb : d130545 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129484, d130545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129484, d130545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129485 q = 1) (hb : d130546 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129485, d130546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129485, d130546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129486 q = 1) (hb : d130547 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129486, d130547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129486, d130547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129487 q = 1) (hb : d130548 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129487, d130548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129487, d130548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23697 (p : Pattern) (ha : d129493 p = 1) (hb : d130560 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129488 q = 1) (hb : d130549 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129488, d130549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129488, d130549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23696 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130555 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129489 q = 1) (hb : d130556 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129489, d130556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129489, d130556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129490 q = 1) (hb : d130557 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129490, d130557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129490, d130557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129491 q = 1) (hb : d130558 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129491, d130558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129491, d130558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129492 q = 1) (hb : d130559 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129492, d130559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129492, d130559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129493 q = 1) (hb : d130560 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129493, d130560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129493, d130560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23698 (p : Pattern) (ha : d129499 p = 1) (hb : d130566 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d130505 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d129478 q = 1) (hb : d130525 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129478, d130525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129478, d130525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23695 q ha hb
  have h3 (q : Pattern) (ha : d129479 q = 1) (hb : d130526 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129479, d130526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129479, d130526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129480 q = 1) (hb : d130527 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129480, d130527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129480, d130527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129481 q = 1) (hb : d130528 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129481, d130528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129481, d130528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129482 q = 1) (hb : d130529 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129482, d130529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129482, d130529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129494 q = 1) (hb : d130561 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129494, d130561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129494, d130561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23697 q ha hb
  have h8 (q : Pattern) (ha : d129495 q = 1) (hb : d130562 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129495, d130562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129495, d130562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129496 q = 1) (hb : d130563 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129496, d130563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129496, d130563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129497 q = 1) (hb : d130564 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129497, d130564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129497, d130564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d129498 q = 1) (hb : d130565 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129498, d130565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129498, d130565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d129499 q = 1) (hb : d130566 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129499, d130566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129499, d130566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro23699 (p : Pattern) (ha : d129505 p = 1) (hb : d130600 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d130584 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d129500 q = 1) (hb : d130589 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129500, d130589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23633 q ha hb
    | true =>
      simp only [d129500, d130589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23628 q ha hb
  have h3 (q : Pattern) (ha : d129501 q = 1) (hb : d130590 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129501, d130590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129501, d130590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d130596 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d129502 q = 1) (hb : d130597 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129502, d130597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129502, d130597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129503 q = 1) (hb : d130598 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129503, d130598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129503, d130598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129504 q = 1) (hb : d130599 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129504, d130599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129504, d130599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129505 q = 1) (hb : d130600 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129505, d130600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129505, d130600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23700 (p : Pattern) (ha : d129511 p = 1) (hb : d130613 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129506 q = 1) (hb : d130601 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129506, d130601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129506, d130601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23699 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130608 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129507 q = 1) (hb : d130609 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129507, d130609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129507, d130609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129508 q = 1) (hb : d130610 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129508, d130610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129508, d130610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129509 q = 1) (hb : d130611 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129509, d130611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129509, d130611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129510 q = 1) (hb : d130612 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129510, d130612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129510, d130612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129511 q = 1) (hb : d130613 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129511, d130613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129511, d130613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23701 (p : Pattern) (ha : d129517 p = 1) (hb : d130619 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129512 q = 1) (hb : d130614 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129512, d130614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129512, d130614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23700 q ha hb
  have h2 (q : Pattern) (ha : d129513 q = 1) (hb : d130615 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129513, d130615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129513, d130615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129514 q = 1) (hb : d130616 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129514, d130616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129514, d130616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129515 q = 1) (hb : d130617 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129515, d130617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129515, d130617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129516 q = 1) (hb : d130618 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129516, d130618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129516, d130618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129517 q = 1) (hb : d130619 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129517, d130619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129517, d130619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23702 (p : Pattern) (ha : d129524 p = 1) (hb : d130654 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d130638 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d129519 q = 1) (hb : d130643 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129519, d130643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23644 q ha hb
    | true =>
      simp only [d129519, d130643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23639 q ha hb
  have h3 (q : Pattern) (ha : d129520 q = 1) (hb : d130644 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129520, d130644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129520, d130644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d130650 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d129521 q = 1) (hb : d130651 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129521, d130651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129521, d130651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129522 q = 1) (hb : d130652 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129522, d130652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129522, d130652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129523 q = 1) (hb : d130653 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129523, d130653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129523, d130653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129524 q = 1) (hb : d130654 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129524, d130654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129524, d130654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23703 (p : Pattern) (ha : d129530 p = 1) (hb : d130667 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129525 q = 1) (hb : d130655 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129525, d130655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129525, d130655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23702 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130662 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129526 q = 1) (hb : d130663 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129526, d130663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129526, d130663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129527 q = 1) (hb : d130664 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129527, d130664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129527, d130664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129528 q = 1) (hb : d130665 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129528, d130665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129528, d130665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129529 q = 1) (hb : d130666 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129529, d130666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129529, d130666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129530 q = 1) (hb : d130667 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129530, d130667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129530, d130667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23704 (p : Pattern) (ha : d129536 p = 1) (hb : d130673 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129531 q = 1) (hb : d130668 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129531, d130668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129531, d130668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23703 q ha hb
  have h2 (q : Pattern) (ha : d129532 q = 1) (hb : d130669 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129532, d130669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129532, d130669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129533 q = 1) (hb : d130670 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129533, d130670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129533, d130670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129534 q = 1) (hb : d130671 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129534, d130671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129534, d130671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129535 q = 1) (hb : d130672 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129535, d130672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129535, d130672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129536 q = 1) (hb : d130673 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129536, d130673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129536, d130673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23705 (p : Pattern) (ha : d129540 p = 1) (hb : d130694 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127507 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9834 q = 1) (hb : d101355 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23316 q ha hb
    | true =>
      simp only [d9834, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
  have h3 (q : Pattern) (ha : d9835 q = 1) (hb : d101356 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9835, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d9836 q = 1) (hb : d101357 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9836, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9851 q = 1) (hb : d101372 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9851, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23319 q ha hb
  have h6 (q : Pattern) (ha : d9852 q = 1) (hb : d101373 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9852, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d9853 q = 1) (hb : d101374 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9853, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9854 q = 1) (hb : d101375 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9854, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9870 q = 1) (hb : d101391 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d9870, d101391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23304 q ha hb
    | true =>
      simp only [d9870, d101391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23306 q ha hb
  have h10 (q : Pattern) (ha : d9871 q = 1) (hb : d101392 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d9871, d101392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9871, d101392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d9872 q = 1) (hb : d101393 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d9872, d101393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9872, d101393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9873 q = 1) (hb : d101394 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d9873, d101394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9873, d101394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d101404 q = 1) (hb : d129539 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d101404, d129539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d101404, d129539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d129540 q = 1) (hb : d130694 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d129540, d130694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129540, d130694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  exact h14 p ha hb
theorem andIntro23706 (p : Pattern) (ha : d129546 p = 1) (hb : d130700 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129541 q = 1) (hb : d130695 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129541, d130695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23705 q ha hb
    | true =>
      simp only [d129541, d130695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129542 q = 1) (hb : d130696 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129542, d130696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129542, d130696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d9876 q = 1) (hb : d130687 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d9876, d130687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23649 q ha hb
    | true =>
      simp only [d9876, d130687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9877 q = 1) (hb : d130688 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d9877, d130688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9877, d130688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129543 q = 1) (hb : d130697 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d129543, d130697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129543, d130697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129544 q = 1) (hb : d130698 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d129544, d130698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129544, d130698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129545 q = 1) (hb : d130699 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d129545, d130699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129545, d130699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d129546 q = 1) (hb : d130700 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d129546, d130700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d129546, d130700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23707 (p : Pattern) (ha : d129552 p = 1) (hb : d130719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d130693 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d129547 q = 1) (hb : d130705 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129547, d130705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23706 q ha hb
    | true =>
      simp only [d129547, d130705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23650 q ha hb
  have h3 (q : Pattern) (ha : d129548 q = 1) (hb : d130706 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129548, d130706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129548, d130706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d130715 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d129549 q = 1) (hb : d130716 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129549, d130716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129549, d130716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129550 q = 1) (hb : d130717 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129550, d130717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129550, d130717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129551 q = 1) (hb : d130718 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129551, d130718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129551, d130718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129552 q = 1) (hb : d130719 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129552, d130719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129552, d130719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23708 (p : Pattern) (ha : d129558 p = 1) (hb : d130732 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129553 q = 1) (hb : d130720 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129553, d130720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129553, d130720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23707 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130727 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129554 q = 1) (hb : d130728 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129554, d130728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129554, d130728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129555 q = 1) (hb : d130729 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129555, d130729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129555, d130729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129556 q = 1) (hb : d130730 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129556, d130730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129556, d130730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129557 q = 1) (hb : d130731 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129557, d130731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129557, d130731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129558 q = 1) (hb : d130732 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129558, d130732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129558, d130732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23709 (p : Pattern) (ha : d129564 p = 1) (hb : d130738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129559 q = 1) (hb : d130733 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129559, d130733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129559, d130733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23708 q ha hb
  have h2 (q : Pattern) (ha : d129560 q = 1) (hb : d130734 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129560, d130734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129560, d130734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129561 q = 1) (hb : d130735 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129561, d130735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129561, d130735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129562 q = 1) (hb : d130736 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129562, d130736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129562, d130736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129563 q = 1) (hb : d130737 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129563, d130737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129563, d130737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129564 q = 1) (hb : d130738 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129564, d130738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129564, d130738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23710 (p : Pattern) (ha : d129569 p = 1) (hb : d130760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127800 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10122 q = 1) (hb : d101549 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23344 q ha hb
    | true =>
      simp only [d10122, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
  have h3 (q : Pattern) (ha : d10123 q = 1) (hb : d101550 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10123, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d10124 q = 1) (hb : d101551 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10124, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10142 q = 1) (hb : d101569 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10142, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23347 q ha hb
  have h6 (q : Pattern) (ha : d10143 q = 1) (hb : d101570 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10143, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d10144 q = 1) (hb : d101571 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10144, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10145 q = 1) (hb : d101572 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10145, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10164 q = 1) (hb : d101591 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10164, d101591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23332 q ha hb
    | true =>
      simp only [d10164, d101591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23334 q ha hb
  have h10 (q : Pattern) (ha : d10165 q = 1) (hb : d101592 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10165, d101592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10165, d101592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d10166 q = 1) (hb : d101593 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10166, d101593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10166, d101593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10167 q = 1) (hb : d101594 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10167, d101594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10167, d101594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d101604 q = 1) (hb : d129568 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d101604, d129568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d101604, d129568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d129569 q = 1) (hb : d130760 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d129569, d130760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129569, d130760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  exact h14 p ha hb
theorem andIntro23711 (p : Pattern) (ha : d129575 p = 1) (hb : d130766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129570 q = 1) (hb : d130761 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129570, d130761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23710 q ha hb
    | true =>
      simp only [d129570, d130761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129571 q = 1) (hb : d130762 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129571, d130762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129571, d130762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10170 q = 1) (hb : d130753 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10170, d130753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23661 q ha hb
    | true =>
      simp only [d10170, d130753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10171 q = 1) (hb : d130754 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10171, d130754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10171, d130754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129572 q = 1) (hb : d130763 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d129572, d130763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129572, d130763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129573 q = 1) (hb : d130764 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d129573, d130764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129573, d130764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129574 q = 1) (hb : d130765 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d129574, d130765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129574, d130765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d129575 q = 1) (hb : d130766 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d129575, d130766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d129575, d130766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23712 (p : Pattern) (ha : d129581 p = 1) (hb : d130785 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d130759 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d129576 q = 1) (hb : d130771 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129576, d130771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23711 q ha hb
    | true =>
      simp only [d129576, d130771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23662 q ha hb
  have h3 (q : Pattern) (ha : d129577 q = 1) (hb : d130772 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129577, d130772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129577, d130772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d130781 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d129578 q = 1) (hb : d130782 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129578, d130782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129578, d130782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129579 q = 1) (hb : d130783 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129579, d130783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129579, d130783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129580 q = 1) (hb : d130784 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129580, d130784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129580, d130784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129581 q = 1) (hb : d130785 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129581, d130785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129581, d130785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23713 (p : Pattern) (ha : d129587 p = 1) (hb : d130798 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129582 q = 1) (hb : d130786 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129582, d130786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129582, d130786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23712 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130793 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129583 q = 1) (hb : d130794 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129583, d130794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129583, d130794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129584 q = 1) (hb : d130795 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129584, d130795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129584, d130795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129585 q = 1) (hb : d130796 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129585, d130796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129585, d130796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129586 q = 1) (hb : d130797 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129586, d130797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129586, d130797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129587 q = 1) (hb : d130798 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129587, d130798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129587, d130798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23714 (p : Pattern) (ha : d129593 p = 1) (hb : d130804 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129588 q = 1) (hb : d130799 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129588, d130799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129588, d130799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23713 q ha hb
  have h2 (q : Pattern) (ha : d129589 q = 1) (hb : d130800 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129589, d130800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129589, d130800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129590 q = 1) (hb : d130801 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129590, d130801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129590, d130801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129591 q = 1) (hb : d130802 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129591, d130802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129591, d130802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129592 q = 1) (hb : d130803 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129592, d130803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129592, d130803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129593 q = 1) (hb : d130804 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129593, d130804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129593, d130804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23715 (p : Pattern) (ha : d129599 p = 1) (hb : d130827 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d128092 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10398 q = 1) (hb : d101719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23370 q ha hb
    | true =>
      simp only [d10398, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
  have h3 (q : Pattern) (ha : d10399 q = 1) (hb : d101720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10399, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d10400 q = 1) (hb : d101721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10400, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10419 q = 1) (hb : d101740 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10419, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23372 q ha hb
  have h6 (q : Pattern) (ha : d10420 q = 1) (hb : d101741 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10420, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d10421 q = 1) (hb : d101742 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10421, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10422 q = 1) (hb : d101743 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10422, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d10441 q = 1) (hb : d101762 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10441, d101762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23360 q ha hb
    | true =>
      simp only [d10441, d101762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23362 q ha hb
  have h10 (q : Pattern) (ha : d10442 q = 1) (hb : d101763 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10442, d101763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10442, d101763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h11 (q : Pattern) (ha : d10443 q = 1) (hb : d101764 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10443, d101764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10443, d101764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10444 q = 1) (hb : d101765 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10444, d101765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10444, d101765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d101775 q = 1) (hb : d129598 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d101775, d129598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d101775, d129598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d129599 q = 1) (hb : d130827 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d129599, d130827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129599, d130827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  exact h14 p ha hb
theorem andIntro23716 (p : Pattern) (ha : d129605 p = 1) (hb : d130833 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129600 q = 1) (hb : d130828 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129600, d130828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23715 q ha hb
    | true =>
      simp only [d129600, d130828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129601 q = 1) (hb : d130829 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129601, d130829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129601, d130829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10447 q = 1) (hb : d130820 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10447, d130820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23673 q ha hb
    | true =>
      simp only [d10447, d130820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10448 q = 1) (hb : d130821 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10448, d130821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10448, d130821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129602 q = 1) (hb : d130830 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d129602, d130830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129602, d130830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129603 q = 1) (hb : d130831 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d129603, d130831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129603, d130831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129604 q = 1) (hb : d130832 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d129604, d130832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129604, d130832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d129605 q = 1) (hb : d130833 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d129605, d130833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d129605, d130833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro23717 (p : Pattern) (ha : d129611 p = 1) (hb : d130852 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d130826 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d129606 q = 1) (hb : d130838 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129606, d130838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23716 q ha hb
    | true =>
      simp only [d129606, d130838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23674 q ha hb
  have h3 (q : Pattern) (ha : d129607 q = 1) (hb : d130839 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129607, d130839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129607, d130839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d130848 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d129608 q = 1) (hb : d130849 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129608, d130849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129608, d130849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129609 q = 1) (hb : d130850 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129609, d130850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129609, d130850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129610 q = 1) (hb : d130851 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129610, d130851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129610, d130851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129611 q = 1) (hb : d130852 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129611, d130852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129611, d130852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23718 (p : Pattern) (ha : d129617 p = 1) (hb : d130865 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129612 q = 1) (hb : d130853 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129612, d130853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129612, d130853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23717 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130860 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129613 q = 1) (hb : d130861 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129613, d130861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129613, d130861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129614 q = 1) (hb : d130862 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129614, d130862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129614, d130862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129615 q = 1) (hb : d130863 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129615, d130863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129615, d130863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129616 q = 1) (hb : d130864 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129616, d130864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129616, d130864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129617 q = 1) (hb : d130865 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129617, d130865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129617, d130865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23719 (p : Pattern) (ha : d129623 p = 1) (hb : d130871 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129618 q = 1) (hb : d130866 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129618, d130866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129618, d130866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23718 q ha hb
  have h2 (q : Pattern) (ha : d129619 q = 1) (hb : d130867 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129619, d130867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129619, d130867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129620 q = 1) (hb : d130868 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129620, d130868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129620, d130868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129621 q = 1) (hb : d130869 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129621, d130869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129621, d130869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129622 q = 1) (hb : d130870 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129622, d130870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129622, d130870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129623 q = 1) (hb : d130871 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129623, d130871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129623, d130871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23720 (p : Pattern) (ha : d129629 p = 1) (hb : d130877 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d129518 q = 1) (hb : d130620 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129518, d130620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23698 q ha hb
    | true =>
      simp only [d129518, d130620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23701 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d129537 q = 1) (hb : d130674 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129537, d130674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129537, d130674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23704 q ha hb
  have h3 (q : Pattern) (ha : d129538 q = 1) (hb : d130675 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129538, d130675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129538, d130675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129565 q = 1) (hb : d130739 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129565, d130739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129565, d130739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23709 q ha hb
  have h5 (q : Pattern) (ha : d129566 q = 1) (hb : d130740 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129566, d130740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129566, d130740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129567 q = 1) (hb : d130741 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129567, d130741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129567, d130741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129594 q = 1) (hb : d130805 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129594, d130805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129594, d130805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23714 q ha hb
  have h8 (q : Pattern) (ha : d129595 q = 1) (hb : d130806 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129595, d130806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129595, d130806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129596 q = 1) (hb : d130807 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129596, d130807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129596, d130807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129597 q = 1) (hb : d130808 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d129597, d130808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129597, d130808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d129624 q = 1) (hb : d130872 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129624, d130872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129624, d130872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23719 q ha hb
  have h12 (q : Pattern) (ha : d129625 q = 1) (hb : d130873 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129625, d130873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129625, d130873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d129626 q = 1) (hb : d130874 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129626, d130874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129626, d130874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d129627 q = 1) (hb : d130875 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d129627, d130875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129627, d130875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d129628 q = 1) (hb : d130876 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d129628, d130876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d129628, d130876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d129629 q = 1) (hb : d130877 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d129629, d130877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d129629, d130877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro23721 (p : Pattern) (ha : d129635 p = 1) (hb : d130883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129630 q = 1) (hb : d130878 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d129630, d130878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23720 q ha hb
    | true =>
      simp only [d129630, d130878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129631 q = 1) (hb : d130879 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d129631, d130879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129631, d130879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129632 q = 1) (hb : d130880 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d129632, d130880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129632, d130880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129633 q = 1) (hb : d130881 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d129633, d130881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129633, d130881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129634 q = 1) (hb : d130882 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d129634, d130882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129634, d130882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129635 q = 1) (hb : d130883 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d129635, d130883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129635, d130883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23722 (p : Pattern) (ha : d129641 p = 1) (hb : d130889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129636 q = 1) (hb : d130884 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d129636, d130884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23721 q ha hb
    | true =>
      simp only [d129636, d130884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129637 q = 1) (hb : d130885 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d129637, d130885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129637, d130885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129638 q = 1) (hb : d130886 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d129638, d130886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129638, d130886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129639 q = 1) (hb : d130887 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d129639, d130887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129639, d130887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129640 q = 1) (hb : d130888 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d129640, d130888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129640, d130888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129641 q = 1) (hb : d130889 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d129641, d130889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129641, d130889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23723 (p : Pattern) (ha : d129647 p = 1) (hb : d130895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129642 q = 1) (hb : d130890 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d129642, d130890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23722 q ha hb
    | true =>
      simp only [d129642, d130890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129643 q = 1) (hb : d130891 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d129643, d130891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129643, d130891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129644 q = 1) (hb : d130892 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d129644, d130892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129644, d130892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129645 q = 1) (hb : d130893 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d129645, d130893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129645, d130893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129646 q = 1) (hb : d130894 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d129646, d130894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129646, d130894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129647 q = 1) (hb : d130895 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d129647, d130895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129647, d130895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23724 (p : Pattern) (ha : d129653 p = 1) (hb : d130901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129648 q = 1) (hb : d130896 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d129648, d130896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23723 q ha hb
    | true =>
      simp only [d129648, d130896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129649 q = 1) (hb : d130897 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d129649, d130897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129649, d130897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129650 q = 1) (hb : d130898 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d129650, d130898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129650, d130898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129651 q = 1) (hb : d130899 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d129651, d130899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129651, d130899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129652 q = 1) (hb : d130900 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d129652, d130900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129652, d130900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129653 q = 1) (hb : d130901 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d129653, d130901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129653, d130901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23725 (p : Pattern) (ha : d129659 p = 1) (hb : d130907 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129654 q = 1) (hb : d130902 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d129654, d130902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23724 q ha hb
    | true =>
      simp only [d129654, d130902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129655 q = 1) (hb : d130903 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d129655, d130903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129655, d130903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129656 q = 1) (hb : d130904 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d129656, d130904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129656, d130904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129657 q = 1) (hb : d130905 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d129657, d130905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129657, d130905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129658 q = 1) (hb : d130906 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d129658, d130906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129658, d130906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129659 q = 1) (hb : d130907 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d129659, d130907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129659, d130907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23726 (p : Pattern) (ha : d129665 p = 1) (hb : d130913 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129660 q = 1) (hb : d130908 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d129660, d130908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23725 q ha hb
    | true =>
      simp only [d129660, d130908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129661 q = 1) (hb : d130909 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d129661, d130909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129661, d130909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129662 q = 1) (hb : d130910 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d129662, d130910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129662, d130910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129663 q = 1) (hb : d130911 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d129663, d130911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129663, d130911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129664 q = 1) (hb : d130912 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d129664, d130912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129664, d130912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129665 q = 1) (hb : d130913 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d129665, d130913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129665, d130913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23727 (p : Pattern) (ha : d129671 p = 1) (hb : d130919 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129666 q = 1) (hb : d130914 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d129666, d130914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23726 q ha hb
    | true =>
      simp only [d129666, d130914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129667 q = 1) (hb : d130915 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d129667, d130915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129667, d130915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129668 q = 1) (hb : d130916 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d129668, d130916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129668, d130916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129669 q = 1) (hb : d130917 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d129669, d130917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129669, d130917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129670 q = 1) (hb : d130918 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d129670, d130918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129670, d130918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129671 q = 1) (hb : d130919 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d129671, d130919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129671, d130919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro23728 (p : Pattern) (ha : d9436 p = 1) (hb : d130924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20420 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9309 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9432 q = 1) (hb : d130920 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d9432, d130920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9432, d130920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20398 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d9433 q = 1) (hb : d130921 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d9433, d130921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9433, d130921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9434 q = 1) (hb : d130922 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d9434, d130922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9434, d130922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d9435 q = 1) (hb : d130923 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d9435, d130923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9435, d130923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d9436 q = 1) (hb : d130924 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d9436, d130924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9436, d130924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23729 (p : Pattern) (ha : d129477 p = 1) (hb : d130930 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9437 q = 1) (hb : d130925 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d9437, d130925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9437, d130925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23728 q ha hb
  have h2 (q : Pattern) (ha : d129473 q = 1) (hb : d130926 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129473, d130926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129473, d130926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129474 q = 1) (hb : d130927 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129474, d130927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129474, d130927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129475 q = 1) (hb : d130928 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129475, d130928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129475, d130928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129476 q = 1) (hb : d130929 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129476, d130929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129476, d130929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129477 q = 1) (hb : d130930 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129477, d130930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129477, d130930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23730 (p : Pattern) (ha : d129487 p = 1) (hb : d130940 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20452 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9342 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129483 q = 1) (hb : d130936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129483, d130936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129483, d130936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20467 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d129484 q = 1) (hb : d130937 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129484, d130937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129484, d130937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129485 q = 1) (hb : d130938 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129485, d130938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129485, d130938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129486 q = 1) (hb : d130939 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129486, d130939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129486, d130939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129487 q = 1) (hb : d130940 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129487, d130940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129487, d130940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23731 (p : Pattern) (ha : d129493 p = 1) (hb : d130946 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129488 q = 1) (hb : d130941 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129488, d130941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129488, d130941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23730 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d20478 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129489 q = 1) (hb : d130942 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129489, d130942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129489, d130942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129490 q = 1) (hb : d130943 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129490, d130943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129490, d130943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129491 q = 1) (hb : d130944 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129491, d130944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129491, d130944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129492 q = 1) (hb : d130945 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129492, d130945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129492, d130945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129493 q = 1) (hb : d130946 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129493, d130946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129493, d130946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23732 (p : Pattern) (ha : d129499 p = 1) (hb : d130952 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d20412 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d129478 q = 1) (hb : d130931 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129478, d130931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129478, d130931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23729 q ha hb
  have h3 (q : Pattern) (ha : d129479 q = 1) (hb : d130932 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129479, d130932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129479, d130932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129480 q = 1) (hb : d130933 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129480, d130933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129480, d130933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129481 q = 1) (hb : d130934 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129481, d130934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129481, d130934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129482 q = 1) (hb : d130935 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129482, d130935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129482, d130935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129494 q = 1) (hb : d130947 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129494, d130947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129494, d130947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23731 q ha hb
  have h8 (q : Pattern) (ha : d129495 q = 1) (hb : d130948 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129495, d130948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129495, d130948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129496 q = 1) (hb : d130949 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129496, d130949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129496, d130949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129497 q = 1) (hb : d130950 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129497, d130950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129497, d130950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d129498 q = 1) (hb : d130951 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129498, d130951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129498, d130951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d129499 q = 1) (hb : d130952 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129499, d130952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129499, d130952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro23733 (p : Pattern) (ha : d129505 p = 1) (hb : d130957 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20507 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d129500 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129501 q = 1) (hb : d130953 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129501, d130953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129501, d130953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20529 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d129502 q = 1) (hb : d130954 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129502, d130954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129502, d130954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129503 q = 1) (hb : d130955 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129503, d130955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129503, d130955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129504 q = 1) (hb : d130956 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129504, d130956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129504, d130956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129505 q = 1) (hb : d130957 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129505, d130957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129505, d130957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23734 (p : Pattern) (ha : d129511 p = 1) (hb : d130963 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129506 q = 1) (hb : d130958 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129506, d130958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129506, d130958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23733 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d20545 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129507 q = 1) (hb : d130959 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129507, d130959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129507, d130959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129508 q = 1) (hb : d130960 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129508, d130960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129508, d130960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129509 q = 1) (hb : d130961 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129509, d130961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129509, d130961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129510 q = 1) (hb : d130962 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129510, d130962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129510, d130962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129511 q = 1) (hb : d130963 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129511, d130963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129511, d130963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23735 (p : Pattern) (ha : d129517 p = 1) (hb : d130969 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129512 q = 1) (hb : d130964 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129512, d130964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129512, d130964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23734 q ha hb
  have h2 (q : Pattern) (ha : d129513 q = 1) (hb : d130965 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129513, d130965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129513, d130965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129514 q = 1) (hb : d130966 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129514, d130966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129514, d130966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129515 q = 1) (hb : d130967 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129515, d130967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129515, d130967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129516 q = 1) (hb : d130968 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129516, d130968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129516, d130968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129517 q = 1) (hb : d130969 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129517, d130969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129517, d130969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23736 (p : Pattern) (ha : d129524 p = 1) (hb : d130975 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20575 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d129519 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129520 q = 1) (hb : d130971 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129520, d130971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129520, d130971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20597 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d129521 q = 1) (hb : d130972 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129521, d130972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129521, d130972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129522 q = 1) (hb : d130973 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129522, d130973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129522, d130973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129523 q = 1) (hb : d130974 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129523, d130974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129523, d130974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129524 q = 1) (hb : d130975 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129524, d130975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129524, d130975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23737 (p : Pattern) (ha : d129530 p = 1) (hb : d130981 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129525 q = 1) (hb : d130976 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129525, d130976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129525, d130976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23736 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d20613 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129526 q = 1) (hb : d130977 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129526, d130977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129526, d130977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129527 q = 1) (hb : d130978 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129527, d130978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129527, d130978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129528 q = 1) (hb : d130979 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129528, d130979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129528, d130979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129529 q = 1) (hb : d130980 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129529, d130980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129529, d130980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129530 q = 1) (hb : d130981 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129530, d130981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129530, d130981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23738 (p : Pattern) (ha : d129536 p = 1) (hb : d130987 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129531 q = 1) (hb : d130982 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129531, d130982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129531, d130982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23737 q ha hb
  have h2 (q : Pattern) (ha : d129532 q = 1) (hb : d130983 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129532, d130983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129532, d130983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129533 q = 1) (hb : d130984 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129533, d130984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129533, d130984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129534 q = 1) (hb : d130985 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129534, d130985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129534, d130985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129535 q = 1) (hb : d130986 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129535, d130986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129535, d130986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129536 q = 1) (hb : d130987 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129536, d130987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129536, d130987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23739 (p : Pattern) (ha : d129552 p = 1) (hb : d130994 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20644 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d129547 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129548 q = 1) (hb : d130990 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129548, d130990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129548, d130990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20669 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d129549 q = 1) (hb : d130991 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129549, d130991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129549, d130991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129550 q = 1) (hb : d130992 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129550, d130992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129550, d130992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129551 q = 1) (hb : d130993 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129551, d130993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129551, d130993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129552 q = 1) (hb : d130994 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129552, d130994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129552, d130994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23740 (p : Pattern) (ha : d129558 p = 1) (hb : d131000 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129553 q = 1) (hb : d130995 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129553, d130995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129553, d130995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23739 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d20685 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129554 q = 1) (hb : d130996 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129554, d130996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129554, d130996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129555 q = 1) (hb : d130997 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129555, d130997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129555, d130997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129556 q = 1) (hb : d130998 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129556, d130998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129556, d130998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129557 q = 1) (hb : d130999 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129557, d130999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129557, d130999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129558 q = 1) (hb : d131000 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129558, d131000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129558, d131000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23741 (p : Pattern) (ha : d129564 p = 1) (hb : d131006 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129559 q = 1) (hb : d131001 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129559, d131001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129559, d131001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23740 q ha hb
  have h2 (q : Pattern) (ha : d129560 q = 1) (hb : d131002 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129560, d131002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129560, d131002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129561 q = 1) (hb : d131003 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129561, d131003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129561, d131003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129562 q = 1) (hb : d131004 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129562, d131004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129562, d131004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129563 q = 1) (hb : d131005 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129563, d131005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129563, d131005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129564 q = 1) (hb : d131006 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129564, d131006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129564, d131006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23742 (p : Pattern) (ha : d129581 p = 1) (hb : d131014 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20717 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d129576 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129577 q = 1) (hb : d131010 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129577, d131010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129577, d131010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20742 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d129578 q = 1) (hb : d131011 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129578, d131011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129578, d131011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129579 q = 1) (hb : d131012 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129579, d131012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129579, d131012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129580 q = 1) (hb : d131013 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129580, d131013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129580, d131013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129581 q = 1) (hb : d131014 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129581, d131014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129581, d131014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23743 (p : Pattern) (ha : d129587 p = 1) (hb : d131020 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129582 q = 1) (hb : d131015 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129582, d131015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129582, d131015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23742 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d20758 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129583 q = 1) (hb : d131016 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129583, d131016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129583, d131016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129584 q = 1) (hb : d131017 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129584, d131017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129584, d131017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129585 q = 1) (hb : d131018 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129585, d131018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129585, d131018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129586 q = 1) (hb : d131019 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129586, d131019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129586, d131019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129587 q = 1) (hb : d131020 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129587, d131020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129587, d131020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23744 (p : Pattern) (ha : d129593 p = 1) (hb : d131026 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129588 q = 1) (hb : d131021 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129588, d131021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129588, d131021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23743 q ha hb
  have h2 (q : Pattern) (ha : d129589 q = 1) (hb : d131022 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129589, d131022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129589, d131022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129590 q = 1) (hb : d131023 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129590, d131023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129590, d131023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129591 q = 1) (hb : d131024 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129591, d131024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129591, d131024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129592 q = 1) (hb : d131025 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129592, d131025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129592, d131025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129593 q = 1) (hb : d131026 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129593, d131026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129593, d131026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23745 (p : Pattern) (ha : d129611 p = 1) (hb : d131035 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20791 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d129606 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129607 q = 1) (hb : d131031 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129607, d131031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129607, d131031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20816 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d129608 q = 1) (hb : d131032 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129608, d131032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129608, d131032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129609 q = 1) (hb : d131033 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129609, d131033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129609, d131033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129610 q = 1) (hb : d131034 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129610, d131034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129610, d131034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129611 q = 1) (hb : d131035 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129611, d131035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129611, d131035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro23746 (p : Pattern) (ha : d129617 p = 1) (hb : d131041 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129612 q = 1) (hb : d131036 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129612, d131036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129612, d131036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23745 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d20832 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129613 q = 1) (hb : d131037 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129613, d131037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129613, d131037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129614 q = 1) (hb : d131038 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129614, d131038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129614, d131038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129615 q = 1) (hb : d131039 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129615, d131039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129615, d131039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129616 q = 1) (hb : d131040 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129616, d131040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129616, d131040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d129617 q = 1) (hb : d131041 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129617, d131041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129617, d131041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro23747 (p : Pattern) (ha : d129623 p = 1) (hb : d131047 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129618 q = 1) (hb : d131042 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129618, d131042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129618, d131042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23746 q ha hb
  have h2 (q : Pattern) (ha : d129619 q = 1) (hb : d131043 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129619, d131043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129619, d131043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129620 q = 1) (hb : d131044 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129620, d131044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129620, d131044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129621 q = 1) (hb : d131045 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129621, d131045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129621, d131045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129622 q = 1) (hb : d131046 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129622, d131046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129622, d131046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129623 q = 1) (hb : d131047 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129623, d131047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129623, d131047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro23748 (p : Pattern) (ha : d129629 p = 1) (hb : d131053 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d129518 q = 1) (hb : d130970 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129518, d130970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23732 q ha hb
    | true =>
      simp only [d129518, d130970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23735 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d129537 q = 1) (hb : d130988 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129537, d130988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129537, d130988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23738 q ha hb
  have h3 (q : Pattern) (ha : d129538 q = 1) (hb : d130989 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129538, d130989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129538, d130989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129565 q = 1) (hb : d131007 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129565, d131007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129565, d131007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23741 q ha hb
  have h5 (q : Pattern) (ha : d129566 q = 1) (hb : d131008 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129566, d131008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129566, d131008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129567 q = 1) (hb : d131009 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129567, d131009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129567, d131009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129594 q = 1) (hb : d131027 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129594, d131027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129594, d131027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23744 q ha hb
  have h8 (q : Pattern) (ha : d129595 q = 1) (hb : d131028 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129595, d131028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129595, d131028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129596 q = 1) (hb : d131029 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129596, d131029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129596, d131029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129597 q = 1) (hb : d131030 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d129597, d131030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129597, d131030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d129624 q = 1) (hb : d131048 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129624, d131048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129624, d131048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23747 q ha hb
  have h12 (q : Pattern) (ha : d129625 q = 1) (hb : d131049 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129625, d131049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129625, d131049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d129626 q = 1) (hb : d131050 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129626, d131050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129626, d131050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d129627 q = 1) (hb : d131051 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d129627, d131051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129627, d131051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d129628 q = 1) (hb : d131052 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d129628, d131052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d129628, d131052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d129629 q = 1) (hb : d131053 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d129629, d131053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d129629, d131053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro23749 (p : Pattern) (ha : d129635 p = 1) (hb : d131059 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129630 q = 1) (hb : d131054 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d129630, d131054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23748 q ha hb
    | true =>
      simp only [d129630, d131054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d129631 q = 1) (hb : d131055 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d129631, d131055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129631, d131055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d129632 q = 1) (hb : d131056 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d129632, d131056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129632, d131056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d129633 q = 1) (hb : d131057 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d129633, d131057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129633, d131057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d129634 q = 1) (hb : d131058 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d129634, d131058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129634, d131058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d129635 q = 1) (hb : d131059 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d129635, d131059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129635, d131059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
