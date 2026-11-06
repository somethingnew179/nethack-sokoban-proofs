import NetHack.Soko22Hazard87.AndIntroBlocks0195
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro49000 (p : Pattern) (ha : d22938 p = 1) (hb : d128048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13813 q = 1) (hb : d113965 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
  have h2 (q : Pattern) (ha : d10353 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13814 q = 1) (hb : d113966 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10355 q = 1) (hb : d101676 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13815 q = 1) (hb : d113967 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13815, d113967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13815, d113967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13816 q = 1) (hb : d113968 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13816, d113968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13816, d113968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d13817 q = 1) (hb : d123728 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13817, d123728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13817, d123728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33547 q ha hb
  have h8 (q : Pattern) (ha : d13678 q = 1) (hb : d101692 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33547 q ha hb
    | true =>
      simp only [d13678, d101692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13818 q = 1) (hb : d123729 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13818, d123729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13818, d123729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13679 q = 1) (hb : d101694 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, d101694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d13679, d101694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13819 q = 1) (hb : d123730 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13819, d123730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13819, d123730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13820 q = 1) (hb : d123731 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13820, d123731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13820, d123731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d13821 q = 1) (hb : d128043 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d13821, d128043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d13821, d128043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d22937 q = 1) (hb : d123732 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22937, d123732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d22937, d123732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d22938 q = 1) (hb : d128048 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22938, d128048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22938, d128048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro49001 (p : Pattern) (ha : d22957 p = 1) (hb : d123748 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22952 q = 1) (hb : d76361 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22952, d76361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22952, d76361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46269 q ha hb
  have h2 (q : Pattern) (ha : d22699 q = 1) (hb : d69331 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22699, d69331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46269 q ha hb
    | true =>
      simp only [d22699, d69331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22953 q = 1) (hb : d76362 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22953, d76362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22953, d76362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22700 q = 1) (hb : d69332 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22700, d69332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22700, d69332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22954 q = 1) (hb : d76363 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22954, d76363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22954, d76363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22955 q = 1) (hb : d76364 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22955, d76364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22955, d76364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22956 q = 1) (hb : d76365 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22956, d76365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22956, d76365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15790 q = 1) (hb : d123743 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
  have h9 (q : Pattern) (ha : d10412 q = 1) (hb : d101733 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
    | true =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15791 q = 1) (hb : d123744 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15791, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15791, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10414 q = 1) (hb : d101735 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15792 q = 1) (hb : d123745 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15792, d123745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15792, d123745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15793 q = 1) (hb : d123746 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15793, d123746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15793, d123746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d15794 q = 1) (hb : d123747 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15794, d123747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15794, d123747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d22957 q = 1) (hb : d123748 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22957, d123748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22957, d123748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro49002 (p : Pattern) (ha : d22963 p = 1) (hb : d128067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22934 q = 1) (hb : d128045 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22934, d128045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48998 q ha hb
    | true =>
      simp only [d22934, d128045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48999 q ha hb
  have h2 (q : Pattern) (ha : d22935 q = 1) (hb : d128046 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22935, d128046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22935, d128046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22936 q = 1) (hb : d128047 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22936, d128047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22936, d128047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22939 q = 1) (hb : d128049 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22939, d128049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48999 q ha hb
    | true =>
      simp only [d22939, d128049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49000 q ha hb
  have h5 (q : Pattern) (ha : d22940 q = 1) (hb : d128050 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22940, d128050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22940, d128050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22941 q = 1) (hb : d128051 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22941, d128051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22941, d128051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22942 q = 1) (hb : d128052 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22942, d128052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22942, d128052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22949 q = 1) (hb : d128059 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22949, d128059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48999 q ha hb
    | true =>
      simp only [d22949, d128059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48973 q ha hb
  have h9 (q : Pattern) (ha : d22950 q = 1) (hb : d128060 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22950, d128060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22950, d128060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22951 q = 1) (hb : d128061 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22951, d128061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22951, d128061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22958 q = 1) (hb : d128062 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22958, d128062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48973 q ha hb
    | true =>
      simp only [d22958, d128062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49001 q ha hb
  have h12 (q : Pattern) (ha : d22959 q = 1) (hb : d128063 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22959, d128063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22959, d128063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d22960 q = 1) (hb : d128064 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22960, d128064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22960, d128064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d22961 q = 1) (hb : d128065 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22961, d128065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22961, d128065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d22962 q = 1) (hb : d128066 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22962, d128066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22962, d128066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d22963 q = 1) (hb : d128067 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22963, d128067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d22963, d128067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro49003 (p : Pattern) (ha : d22968 p = 1) (hb : d128072 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22949 q = 1) (hb : d128059 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22949, d128059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48999 q ha hb
    | true =>
      simp only [d22949, d128059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48973 q ha hb
  have h2 (q : Pattern) (ha : d22950 q = 1) (hb : d128060 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22950, d128060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22950, d128060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22951 q = 1) (hb : d128061 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22951, d128061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22951, d128061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22958 q = 1) (hb : d128062 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22958, d128062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48973 q ha hb
    | true =>
      simp only [d22958, d128062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49001 q ha hb
  have h5 (q : Pattern) (ha : d22959 q = 1) (hb : d128063 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22959, d128063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22959, d128063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22960 q = 1) (hb : d128064 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22960, d128064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22960, d128064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22961 q = 1) (hb : d128065 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22961, d128065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22961, d128065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22966 q = 1) (hb : d128070 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22966, d128070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22966, d128070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22967 q = 1) (hb : d128071 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d22967, d128071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22967, d128071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22968 q = 1) (hb : d128072 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d22968, d128072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22968, d128072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro49004 (p : Pattern) (ha : d22974 p = 1) (hb : d128078 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22964 q = 1) (hb : d128068 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22964, d128068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49002 q ha hb
    | true =>
      simp only [d22964, d128068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22965 q = 1) (hb : d128069 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22965, d128069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22965, d128069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22969 q = 1) (hb : d128073 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22969, d128073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49003 q ha hb
    | true =>
      simp only [d22969, d128073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22970 q = 1) (hb : d128074 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22970, d128074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22970, d128074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22971 q = 1) (hb : d128075 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22971, d128075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22971, d128075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22972 q = 1) (hb : d128076 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22972, d128076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22972, d128076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22973 q = 1) (hb : d128077 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22973, d128077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22973, d128077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22974 q = 1) (hb : d128078 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22974, d128078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22974, d128078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49005 (p : Pattern) (ha : d22988 p = 1) (hb : d128090 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22969 q = 1) (hb : d128073 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22969, d128073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49003 q ha hb
    | true =>
      simp only [d22969, d128073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22970 q = 1) (hb : d128074 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22970, d128074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22970, d128074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22983 q = 1) (hb : d128085 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22983, d128085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48975 q ha hb
    | true =>
      simp only [d22983, d128085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22984 q = 1) (hb : d128086 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22984, d128086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22984, d128086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d22985 q = 1) (hb : d128087 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d22985, d128087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22985, d128087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22986 q = 1) (hb : d128088 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d22986, d128088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22986, d128088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22987 q = 1) (hb : d128089 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d22987, d128089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22987, d128089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22988 q = 1) (hb : d128090 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d22988, d128090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22988, d128090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49006 (p : Pattern) (ha : d23051 p = 1) (hb : d128111 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22949 q = 1) (hb : d128059 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22949, d128059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48999 q ha hb
    | true =>
      simp only [d22949, d128059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48973 q ha hb
  have h2 (q : Pattern) (ha : d22950 q = 1) (hb : d128060 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22950, d128060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22950, d128060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22951 q = 1) (hb : d128061 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22951, d128061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22951, d128061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22958 q = 1) (hb : d128062 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22958, d128062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48973 q ha hb
    | true =>
      simp only [d22958, d128062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49001 q ha hb
  have h5 (q : Pattern) (ha : d22959 q = 1) (hb : d128063 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22959, d128063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22959, d128063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22960 q = 1) (hb : d128064 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22960, d128064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22960, d128064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22961 q = 1) (hb : d128065 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22961, d128065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22961, d128065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d23046 q = 1) (hb : d128106 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d23046, d128106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48973 q ha hb
    | true =>
      simp only [d23046, d128106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro46313 q ha hb
  have h9 (q : Pattern) (ha : d23047 q = 1) (hb : d128107 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d23047, d128107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23047, d128107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23048 q = 1) (hb : d128108 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d23048, d128108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23048, d128108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d23049 q = 1) (hb : d128109 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d23049, d128109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d23049, d128109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d23050 q = 1) (hb : d128110 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d23050, d128110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d23050, d128110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d23051 q = 1) (hb : d128111 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d23051, d128111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d23051, d128111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro49007 (p : Pattern) (ha : d23057 p = 1) (hb : d128117 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d23052 q = 1) (hb : d128112 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d23052, d128112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49006 q ha hb
    | true =>
      simp only [d23052, d128112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d23053 q = 1) (hb : d128113 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d23053, d128113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23053, d128113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d23054 q = 1) (hb : d128114 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d23054, d128114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d23054, d128114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d23055 q = 1) (hb : d128115 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d23055, d128115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d23055, d128115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23056 q = 1) (hb : d128116 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d23056, d128116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23056, d128116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d23057 q = 1) (hb : d128117 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d23057, d128117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d23057, d128117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49008 (p : Pattern) (ha : d128123 p = 1) (hb : d150266 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22989 q = 1) (hb : d128091 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22989, d128091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49004 q ha hb
    | true =>
      simp only [d22989, d128091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49005 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d128104 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128105 q = 1) (hb : d150262 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128105, d150262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128105, d150262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d23058 q = 1) (hb : d128118 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d23058, d128118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49007 q ha hb
    | true =>
      simp only [d23058, d128118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d23059 q = 1) (hb : d128119 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d23059, d128119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d23059, d128119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128120 q = 1) (hb : d150263 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128120, d150263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128120, d150263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d128121 q = 1) (hb : d150264 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128121, d150264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128121, d150264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128122 q = 1) (hb : d150265 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128122, d150265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128122, d150265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128123 q = 1) (hb : d150266 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128123, d150266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128123, d150266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro49009 (p : Pattern) (ha : d128136 p = 1) (hb : d150272 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22737 q = 1) (hb : d127897 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22737, d127897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22737, d127897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48964 q ha hb
  have h2 (q : Pattern) (ha : d22738 q = 1) (hb : d127898 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d22738, d127898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22738, d127898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22747 q = 1) (hb : d127907 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22747, d127907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48964 q ha hb
    | true =>
      simp only [d22747, d127907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48967 q ha hb
  have h4 (q : Pattern) (ha : d22748 q = 1) (hb : d127908 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d22748, d127908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22748, d127908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22749 q = 1) (hb : d127909 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d22749, d127909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22749, d127909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127999 q = 1) (hb : d150250 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127999, d150250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48988 q ha hb
    | true =>
      simp only [d127999, d150250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48996 q ha hb
  have h7 (q : Pattern) (ha : d22916 q = 1) (hb : d128017 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22916, d128017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48970 q ha hb
    | true =>
      simp only [d22916, d128017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48971 q ha hb
  have h8 (q : Pattern) (ha : d128018 q = 1) (hb : d150251 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128018, d150251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128018, d150251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d128019 q = 1) (hb : d150252 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128019, d150252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128019, d150252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d128020 q = 1) (hb : d150253 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128020, d150253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d128020, d150253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128024 q = 1) (hb : d150257 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128024, d150257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128024, d150257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48997 q ha hb
  have h12 (q : Pattern) (ha : d22925 q = 1) (hb : d128026 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22925, d128026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22925, d128026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48972 q ha hb
  have h13 (q : Pattern) (ha : d128027 q = 1) (hb : d150258 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128027, d150258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128027, d150258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d128028 q = 1) (hb : d150259 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128028, d150259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128028, d150259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d128029 q = 1) (hb : d150260 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128029, d150260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128029, d150260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d128030 q = 1) (hb : d150261 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128030, d150261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128030, d150261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128124 q = 1) (hb : d150267 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128124, d150267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128124, d150267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49008 q ha hb
  have h18 (q : Pattern) (ha : d23075 q = 1) (hb : d128131 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d23075, d128131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d23075, d128131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48977 q ha hb
  have h19 (q : Pattern) (ha : d128132 q = 1) (hb : d150268 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128132, d150268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128132, d150268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d128133 q = 1) (hb : d150269 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128133, d150269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d128133, d150269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d128134 q = 1) (hb : d150270 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128134, d150270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128134, d150270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d128135 q = 1) (hb : d150271 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128135, d150271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128135, d150271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d128136 q = 1) (hb : d150272 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128136, d150272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128136, d150272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro49010 (p : Pattern) (ha : d128142 p = 1) (hb : d150278 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128137 q = 1) (hb : d150273 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128137, d150273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128137, d150273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49009 q ha hb
  have h2 (q : Pattern) (ha : d128138 q = 1) (hb : d150274 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128138, d150274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128138, d150274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128139 q = 1) (hb : d150275 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128139, d150275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128139, d150275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128140 q = 1) (hb : d150276 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128140, d150276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128140, d150276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128141 q = 1) (hb : d150277 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128141, d150277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128141, d150277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128142 q = 1) (hb : d150278 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128142, d150278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128142, d150278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49011 (p : Pattern) (ha : d128148 p = 1) (hb : d150284 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d127103 q = 1) (hb : d150113 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d127103, d150113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48753 q ha hb
    | true =>
      simp only [d127103, d150113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48795 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127274 q = 1) (hb : d150153 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d127274, d150153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127274, d150153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48842 q ha hb
  have h3 (q : Pattern) (ha : d127275 q = 1) (hb : d150154 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d127275, d150154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d127275, d150154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127558 q = 1) (hb : d150194 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d127558, d150194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127558, d150194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48899 q ha hb
  have h5 (q : Pattern) (ha : d127559 q = 1) (hb : d150195 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d127559, d150195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127559, d150195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127560 q = 1) (hb : d150196 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d127560, d150196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127560, d150196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127851 q = 1) (hb : d150236 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d127851, d150236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127851, d150236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48955 q ha hb
  have h8 (q : Pattern) (ha : d127852 q = 1) (hb : d150237 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d127852, d150237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127852, d150237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d127853 q = 1) (hb : d150238 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d127853, d150238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127853, d150238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d127854 q = 1) (hb : d150239 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d127854, d150239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127854, d150239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128143 q = 1) (hb : d150279 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128143, d150279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128143, d150279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49010 q ha hb
  have h12 (q : Pattern) (ha : d128144 q = 1) (hb : d150280 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128144, d150280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128144, d150280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128145 q = 1) (hb : d150281 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128145, d150281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128145, d150281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128146 q = 1) (hb : d150282 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d128146, d150282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128146, d150282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128147 q = 1) (hb : d150283 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d128147, d150283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128147, d150283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128148 q = 1) (hb : d150284 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d128148, d150284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128148, d150284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro49012 (p : Pattern) (ha : d128154 p = 1) (hb : d150290 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128149 q = 1) (hb : d150285 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d128149, d150285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49011 q ha hb
    | true =>
      simp only [d128149, d150285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128150 q = 1) (hb : d150286 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d128150, d150286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128150, d150286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128151 q = 1) (hb : d150287 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d128151, d150287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128151, d150287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128152 q = 1) (hb : d150288 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d128152, d150288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128152, d150288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128153 q = 1) (hb : d150289 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d128153, d150289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128153, d150289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128154 q = 1) (hb : d150290 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d128154, d150290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128154, d150290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49013 (p : Pattern) (ha : d128160 p = 1) (hb : d150296 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128155 q = 1) (hb : d150291 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d128155, d150291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49012 q ha hb
    | true =>
      simp only [d128155, d150291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128156 q = 1) (hb : d150292 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d128156, d150292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128156, d150292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128157 q = 1) (hb : d150293 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d128157, d150293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128157, d150293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128158 q = 1) (hb : d150294 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d128158, d150294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128158, d150294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128159 q = 1) (hb : d150295 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d128159, d150295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128159, d150295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128160 q = 1) (hb : d150296 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d128160, d150296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128160, d150296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49014 (p : Pattern) (ha : d128166 p = 1) (hb : d150302 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128161 q = 1) (hb : d150297 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d128161, d150297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49013 q ha hb
    | true =>
      simp only [d128161, d150297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128162 q = 1) (hb : d150298 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d128162, d150298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128162, d150298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128163 q = 1) (hb : d150299 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d128163, d150299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128163, d150299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128164 q = 1) (hb : d150300 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d128164, d150300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128164, d150300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128165 q = 1) (hb : d150301 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d128165, d150301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128165, d150301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128166 q = 1) (hb : d150302 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d128166, d150302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128166, d150302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49015 (p : Pattern) (ha : d128172 p = 1) (hb : d150308 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128167 q = 1) (hb : d150303 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d128167, d150303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49014 q ha hb
    | true =>
      simp only [d128167, d150303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128168 q = 1) (hb : d150304 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d128168, d150304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128168, d150304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128169 q = 1) (hb : d150305 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d128169, d150305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128169, d150305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128170 q = 1) (hb : d150306 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d128170, d150306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128170, d150306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128171 q = 1) (hb : d150307 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d128171, d150307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128171, d150307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128172 q = 1) (hb : d150308 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d128172, d150308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128172, d150308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49016 (p : Pattern) (ha : d128178 p = 1) (hb : d150314 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128173 q = 1) (hb : d150309 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d128173, d150309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49015 q ha hb
    | true =>
      simp only [d128173, d150309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128174 q = 1) (hb : d150310 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d128174, d150310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128174, d150310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128175 q = 1) (hb : d150311 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d128175, d150311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128175, d150311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128176 q = 1) (hb : d150312 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d128176, d150312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128176, d150312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128177 q = 1) (hb : d150313 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d128177, d150313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128177, d150313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128178 q = 1) (hb : d150314 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d128178, d150314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128178, d150314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49017 (p : Pattern) (ha : d128184 p = 1) (hb : d150320 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128179 q = 1) (hb : d150315 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d128179, d150315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49016 q ha hb
    | true =>
      simp only [d128179, d150315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128180 q = 1) (hb : d150316 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d128180, d150316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128180, d150316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128181 q = 1) (hb : d150317 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d128181, d150317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128181, d150317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128182 q = 1) (hb : d150318 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d128182, d150318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128182, d150318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128183 q = 1) (hb : d150319 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d128183, d150319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128183, d150319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128184 q = 1) (hb : d150320 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d128184, d150320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128184, d150320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49018 (p : Pattern) (ha : d128190 p = 1) (hb : d150326 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128185 q = 1) (hb : d150321 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d128185, d150321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49017 q ha hb
    | true =>
      simp only [d128185, d150321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128186 q = 1) (hb : d150322 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d128186, d150322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128186, d150322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128187 q = 1) (hb : d150323 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d128187, d150323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128187, d150323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128188 q = 1) (hb : d150324 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d128188, d150324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128188, d150324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128189 q = 1) (hb : d150325 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d128189, d150325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128189, d150325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128190 q = 1) (hb : d150326 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d128190, d150326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128190, d150326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49019 (p : Pattern) (ha : d194574 p = 1) (hb : d207963 p = 1) : d194574 p = 1 := by
  have h0 (q : Pattern) (ha : d194574 q = 1) (hb : d207963 q = 1) : d194574 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro49020 (p : Pattern) (ha : d20966 p = 1) (hb : d126892 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d126887 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20906 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48721 q ha hb
    | true =>
      simp only [d20906, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h5 (q : Pattern) (ha : d20962 q = 1) (hb : d126888 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20962, d126888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20962, d126888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d20963 q = 1) (hb : d126889 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20963, d126889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20963, d126889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20964 q = 1) (hb : d126890 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20964, d126890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20964, d126890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20965 q = 1) (hb : d126891 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20965, d126891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20965, d126891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20966 q = 1) (hb : d126892 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20966, d126892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20966, d126892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro49021 (p : Pattern) (ha : d20973 p = 1) (hb : d126899 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52099 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52105 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126887 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d20906 q = 1) (hb : d52008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48721 q ha hb
    | true =>
      simp only [d20906, d52008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h4 (q : Pattern) (ha : d20962 q = 1) (hb : d126888 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20962, d126888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20962, d126888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d74076 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d20963 q = 1) (hb : d126889 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20963, d126889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20963, d126889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20964 q = 1) (hb : d126890 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20964, d126890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20964, d126890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20965 q = 1) (hb : d126891 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20965, d126891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20965, d126891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52148 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d52152 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d126894 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d20913 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20913, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48723 q ha hb
    | true =>
      simp only [d20913, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h13 (q : Pattern) (ha : d20969 q = 1) (hb : d126895 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20969, d126895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d20969, d126895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d20970 q = 1) (hb : d126896 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20970, d126896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d20970, d126896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d20971 q = 1) (hb : d126897 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20971, d126897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20971, d126897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d20972 q = 1) (hb : d126898 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20972, d126898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20972, d126898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d20973 q = 1) (hb : d126899 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20973, d126899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20973, d126899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro49022 (p : Pattern) (ha : d126906 p = 1) (hb : d194340 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d126894 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20913 q = 1) (hb : d52024 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20913, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48723 q ha hb
    | true =>
      simp only [d20913, d52024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h3 (q : Pattern) (ha : d20969 q = 1) (hb : d126895 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20969, d126895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20969, d126895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74083 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d20970 q = 1) (hb : d126896 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20970, d126896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20970, d126896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20971 q = 1) (hb : d126904 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20971, d126904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20971, d126904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20972 q = 1) (hb : d126905 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20972, d126905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20972, d126905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d126906 q = 1) (hb : d194340 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d126906, d194340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126906, d194340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro49023 (p : Pattern) (ha : d126930 p = 1) (hb : d194350 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d126925 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20945 q = 1) (hb : d52062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20945, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48728 q ha hb
    | true =>
      simp only [d20945, d52062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
  have h3 (q : Pattern) (ha : d126926 q = 1) (hb : d194346 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d126926, d194346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d126926, d194346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d74105 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d126927 q = 1) (hb : d194347 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126927, d194347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d126927, d194347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d126928 q = 1) (hb : d194348 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d126928, d194348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126928, d194348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126929 q = 1) (hb : d194349 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d126929, d194349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126929, d194349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d126930 q = 1) (hb : d194350 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d126930, d194350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126930, d194350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49024 (p : Pattern) (ha : d126936 p = 1) (hb : d194356 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52093 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20974 q = 1) (hb : d126900 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20974, d126900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49020 q ha hb
    | true =>
      simp only [d20974, d126900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49021 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d52164 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d20975 q = 1) (hb : d126901 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20975, d126901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20975, d126901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d126902 q = 1) (hb : d194338 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d126902, d194338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d126902, d194338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d126903 q = 1) (hb : d194339 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d126903, d194339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d126903, d194339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126907 q = 1) (hb : d194341 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d126907, d194341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d126907, d194341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49022 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d126908 q = 1) (hb : d194342 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d126908, d194342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d126908, d194342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d126909 q = 1) (hb : d194343 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d126909, d194343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d126909, d194343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d126910 q = 1) (hb : d194344 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d126910, d194344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d126910, d194344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d126911 q = 1) (hb : d194345 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d126911, d194345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126911, d194345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d126931 q = 1) (hb : d194351 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d126931, d194351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d126931, d194351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49023 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d126932 q = 1) (hb : d194352 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d126932, d194352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d126932, d194352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d126933 q = 1) (hb : d194353 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d126933, d194353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d126933, d194353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d126934 q = 1) (hb : d194354 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d126934, d194354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d126934, d194354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d126935 q = 1) (hb : d194355 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d126935, d194355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d126935, d194355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d126936 q = 1) (hb : d194356 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d126936, d194356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d126936, d194356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro49025 (p : Pattern) (ha : d126942 p = 1) (hb : d194362 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d52074 q = 1) (hb : d53648 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d52074, d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52074, d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro327 q ha hb
  have h3 (q : Pattern) (ha : d52075 q = 1) (hb : d53649 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d52075, d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52075, d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52076 q = 1) (hb : d53650 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d52076, d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52076, d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d52077 q = 1) (hb : d53651 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d52077, d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d52077, d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d52078 q = 1) (hb : d53652 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d52078, d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d52078, d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d126937 q = 1) (hb : d194357 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d126937, d194357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d126937, d194357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49024 q ha hb
  have h8 (q : Pattern) (ha : d126938 q = 1) (hb : d194358 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d126938, d194358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d126938, d194358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d126939 q = 1) (hb : d194359 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d126939, d194359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d126939, d194359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d126940 q = 1) (hb : d194360 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d126940, d194360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d126940, d194360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d126941 q = 1) (hb : d194361 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d126941, d194361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d126941, d194361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d126942 q = 1) (hb : d194362 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d126942, d194362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d126942, d194362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro49026 (p : Pattern) (ha : d21151 p = 1) (hb : d127013 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d126974 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d126980 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d127002 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d21146 q = 1) (hb : d126951 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21146, d126951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48756 q ha hb
    | true =>
      simp only [d21146, d126951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48757 q ha hb
  have h5 (q : Pattern) (ha : d21147 q = 1) (hb : d127003 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21147, d127003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21147, d127003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d127009 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d21148 q = 1) (hb : d127010 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21148, d127010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21148, d127010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21149 q = 1) (hb : d127011 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21149, d127011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21149, d127011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21150 q = 1) (hb : d127012 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21150, d127012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21150, d127012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21151 q = 1) (hb : d127013 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21151, d127013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21151, d127013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro49027 (p : Pattern) (ha : d21161 p = 1) (hb : d127032 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d126974 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d126980 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127002 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d21146 q = 1) (hb : d126951 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21146, d126951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48756 q ha hb
    | true =>
      simp only [d21146, d126951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48757 q ha hb
  have h4 (q : Pattern) (ha : d21147 q = 1) (hb : d127003 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21147, d127003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21147, d127003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d127009 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d21148 q = 1) (hb : d127010 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21148, d127010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21148, d127010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21149 q = 1) (hb : d127011 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21149, d127011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21149, d127011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21150 q = 1) (hb : d127012 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21150, d127012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21150, d127012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d127018 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d127022 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d127024 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d21156 q = 1) (hb : d126960 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21156, d126960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48759 q ha hb
    | true =>
      simp only [d21156, d126960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48760 q ha hb
  have h13 (q : Pattern) (ha : d21157 q = 1) (hb : d127025 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21157, d127025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21157, d127025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d127028 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d21158 q = 1) (hb : d127029 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21158, d127029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21158, d127029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d21159 q = 1) (hb : d127030 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21159, d127030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21159, d127030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21160 q = 1) (hb : d127031 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21160, d127031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21160, d127031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d21161 q = 1) (hb : d127032 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21161, d127032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21161, d127032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro49028 (p : Pattern) (ha : d127041 p = 1) (hb : d194365 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127024 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21156 q = 1) (hb : d126960 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21156, d126960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48759 q ha hb
    | true =>
      simp only [d21156, d126960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48760 q ha hb
  have h3 (q : Pattern) (ha : d21157 q = 1) (hb : d127025 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21157, d127025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21157, d127025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d127028 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21158 q = 1) (hb : d127029 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21158, d127029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21158, d127029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21159 q = 1) (hb : d127039 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21159, d127039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21159, d127039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21160 q = 1) (hb : d127040 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21160, d127040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21160, d127040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127041 q = 1) (hb : d194365 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127041, d194365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127041, d194365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro49029 (p : Pattern) (ha : d127090 p = 1) (hb : d194376 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127078 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127079 q = 1) (hb : d194371 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127079, d194371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48791 q hb ha
    | true =>
      simp only [d127079, d194371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48766 q hb ha
  have h3 (q : Pattern) (ha : d127080 q = 1) (hb : d194372 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127080, d194372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127080, d194372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d127086 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d127087 q = 1) (hb : d194373 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127087, d194373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127087, d194373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127088 q = 1) (hb : d194374 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127088, d194374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127088, d194374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127089 q = 1) (hb : d194375 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127089, d194375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127089, d194375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127090 q = 1) (hb : d194376 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127090, d194376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127090, d194376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49030 (p : Pattern) (ha : d127096 p = 1) (hb : d194382 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d126968 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21162 q = 1) (hb : d127033 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21162, d127033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49026 q ha hb
    | true =>
      simp only [d21162, d127033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49027 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127035 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d21163 q = 1) (hb : d127036 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21163, d127036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21163, d127036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d127037 q = 1) (hb : d194363 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127037, d194363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d127037, d194363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127038 q = 1) (hb : d194364 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127038, d194364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127038, d194364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127042 q = 1) (hb : d194366 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127042, d194366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d127042, d194366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49028 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52358 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d127043 q = 1) (hb : d194367 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127043, d194367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127043, d194367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d127044 q = 1) (hb : d194368 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127044, d194368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d127044, d194368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d127045 q = 1) (hb : d194369 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127045, d194369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d127045, d194369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d127046 q = 1) (hb : d194370 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d127046, d194370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127046, d194370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d127091 q = 1) (hb : d194377 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127091, d194377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d127091, d194377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49029 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52414 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d127092 q = 1) (hb : d194378 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127092, d194378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d127092, d194378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d127093 q = 1) (hb : d194379 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127093, d194379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d127093, d194379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d127094 q = 1) (hb : d194380 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127094, d194380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d127094, d194380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d127095 q = 1) (hb : d194381 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d127095, d194381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d127095, d194381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d127096 q = 1) (hb : d194382 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d127096, d194382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d127096, d194382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro49031 (p : Pattern) (ha : d127102 p = 1) (hb : d194388 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127097 q = 1) (hb : d194383 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d127097, d194383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127097, d194383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49030 q ha hb
  have h2 (q : Pattern) (ha : d127098 q = 1) (hb : d194384 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d127098, d194384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127098, d194384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127099 q = 1) (hb : d194385 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d127099, d194385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127099, d194385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127100 q = 1) (hb : d194386 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d127100, d194386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127100, d194386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127101 q = 1) (hb : d194387 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d127101, d194387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127101, d194387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127102 q = 1) (hb : d194388 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d127102, d194388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127102, d194388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49032 (p : Pattern) (ha : d21450 p = 1) (hb : d127179 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127140 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127146 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d127168 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d21445 q = 1) (hb : d127117 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21445, d127117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48800 q ha hb
    | true =>
      simp only [d21445, d127117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48801 q ha hb
  have h5 (q : Pattern) (ha : d21446 q = 1) (hb : d127169 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21446, d127169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21446, d127169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d127175 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d21447 q = 1) (hb : d127176 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21447, d127176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21447, d127176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21448 q = 1) (hb : d127177 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21448, d127177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21448, d127177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21449 q = 1) (hb : d127178 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21449, d127178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21449, d127178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21450 q = 1) (hb : d127179 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21450, d127179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21450, d127179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro49033 (p : Pattern) (ha : d21460 p = 1) (hb : d127198 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127140 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127146 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127168 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d21445 q = 1) (hb : d127117 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21445, d127117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48800 q ha hb
    | true =>
      simp only [d21445, d127117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48801 q ha hb
  have h4 (q : Pattern) (ha : d21446 q = 1) (hb : d127169 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21446, d127169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21446, d127169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d127175 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d21447 q = 1) (hb : d127176 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21447, d127176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21447, d127176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21448 q = 1) (hb : d127177 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21448, d127177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21448, d127177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21449 q = 1) (hb : d127178 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21449, d127178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21449, d127178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d127184 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d127188 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d127190 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d21455 q = 1) (hb : d127126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21455, d127126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48803 q ha hb
    | true =>
      simp only [d21455, d127126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48804 q ha hb
  have h13 (q : Pattern) (ha : d21456 q = 1) (hb : d127191 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21456, d127191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21456, d127191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d127194 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d21457 q = 1) (hb : d127195 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21457, d127195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21457, d127195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d21458 q = 1) (hb : d127196 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21458, d127196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21458, d127196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21459 q = 1) (hb : d127197 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21459, d127197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21459, d127197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d21460 q = 1) (hb : d127198 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21460, d127198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21460, d127198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro49034 (p : Pattern) (ha : d127207 p = 1) (hb : d194392 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127190 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21455 q = 1) (hb : d127126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21455, d127126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48803 q ha hb
    | true =>
      simp only [d21455, d127126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48804 q ha hb
  have h3 (q : Pattern) (ha : d21456 q = 1) (hb : d127191 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21456, d127191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21456, d127191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d127194 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21457 q = 1) (hb : d127195 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21457, d127195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21457, d127195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21458 q = 1) (hb : d127205 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21458, d127205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21458, d127205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21459 q = 1) (hb : d127206 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21459, d127206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21459, d127206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127207 q = 1) (hb : d194392 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127207, d194392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127207, d194392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro49035 (p : Pattern) (ha : d127261 p = 1) (hb : d194403 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127249 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127250 q = 1) (hb : d194398 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127250, d194398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48838 q hb ha
    | true =>
      simp only [d127250, d194398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48811 q hb ha
  have h3 (q : Pattern) (ha : d127251 q = 1) (hb : d194399 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127251, d194399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127251, d194399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d127257 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d127258 q = 1) (hb : d194400 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127258, d194400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127258, d194400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127259 q = 1) (hb : d194401 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127259, d194401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127259, d194401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127260 q = 1) (hb : d194402 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127260, d194402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127260, d194402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127261 q = 1) (hb : d194403 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127261, d194403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127261, d194403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49036 (p : Pattern) (ha : d127267 p = 1) (hb : d194409 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127134 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21461 q = 1) (hb : d127199 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21461, d127199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49032 q ha hb
    | true =>
      simp only [d21461, d127199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49033 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127201 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d21462 q = 1) (hb : d127202 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21462, d127202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21462, d127202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d127203 q = 1) (hb : d194390 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127203, d194390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d127203, d194390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127204 q = 1) (hb : d194391 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127204, d194391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127204, d194391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127208 q = 1) (hb : d194393 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127208, d194393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d127208, d194393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49034 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52579 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d127209 q = 1) (hb : d194394 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127209, d194394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127209, d194394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d127210 q = 1) (hb : d194395 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127210, d194395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d127210, d194395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d127211 q = 1) (hb : d194396 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127211, d194396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d127211, d194396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d127212 q = 1) (hb : d194397 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d127212, d194397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127212, d194397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d127262 q = 1) (hb : d194404 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127262, d194404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d127262, d194404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49035 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52651 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d127263 q = 1) (hb : d194405 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127263, d194405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d127263, d194405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d127264 q = 1) (hb : d194406 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127264, d194406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d127264, d194406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d127265 q = 1) (hb : d194407 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127265, d194407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d127265, d194407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d127266 q = 1) (hb : d194408 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d127266, d194408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d127266, d194408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d127267 q = 1) (hb : d194409 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d127267, d194409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d127267, d194409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro49037 (p : Pattern) (ha : d127273 p = 1) (hb : d194415 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127268 q = 1) (hb : d194410 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d127268, d194410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127268, d194410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49036 q ha hb
  have h2 (q : Pattern) (ha : d127269 q = 1) (hb : d194411 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d127269, d194411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127269, d194411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127270 q = 1) (hb : d194412 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d127270, d194412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127270, d194412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127271 q = 1) (hb : d194413 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d127271, d194413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127271, d194413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127272 q = 1) (hb : d194414 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d127272, d194414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127272, d194414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127273 q = 1) (hb : d194415 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d127273, d194415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127273, d194415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49038 (p : Pattern) (ha : d21803 p = 1) (hb : d127395 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127335 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127344 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d127376 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d21798 q = 1) (hb : d127309 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21798, d127309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48850 q ha hb
    | true =>
      simp only [d21798, d127309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48851 q ha hb
  have h5 (q : Pattern) (ha : d21799 q = 1) (hb : d127377 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21799, d127377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21799, d127377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d127391 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d21800 q = 1) (hb : d127392 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21800, d127392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21800, d127392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21801 q = 1) (hb : d127393 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21801, d127393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21801, d127393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21802 q = 1) (hb : d127394 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21802, d127394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21802, d127394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21803 q = 1) (hb : d127395 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21803, d127395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21803, d127395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro49039 (p : Pattern) (ha : d21813 p = 1) (hb : d127417 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127335 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127344 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127376 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d21798 q = 1) (hb : d127309 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21798, d127309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48850 q ha hb
    | true =>
      simp only [d21798, d127309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48851 q ha hb
  have h4 (q : Pattern) (ha : d21799 q = 1) (hb : d127377 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21799, d127377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21799, d127377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d127391 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d21800 q = 1) (hb : d127392 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21800, d127392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21800, d127392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21801 q = 1) (hb : d127393 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21801, d127393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21801, d127393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21802 q = 1) (hb : d127394 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21802, d127394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21802, d127394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d127401 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d127406 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d127409 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d21808 q = 1) (hb : d127319 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21808, d127319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48853 q ha hb
    | true =>
      simp only [d21808, d127319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48854 q ha hb
  have h13 (q : Pattern) (ha : d21809 q = 1) (hb : d127410 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21809, d127410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21809, d127410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d127413 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d21810 q = 1) (hb : d127414 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21810, d127414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21810, d127414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d21811 q = 1) (hb : d127415 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21811, d127415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21811, d127415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21812 q = 1) (hb : d127416 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21812, d127416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21812, d127416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d21813 q = 1) (hb : d127417 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21813, d127417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21813, d127417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro49040 (p : Pattern) (ha : d127442 p = 1) (hb : d194420 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127409 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21808 q = 1) (hb : d127319 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21808, d127319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48853 q ha hb
    | true =>
      simp only [d21808, d127319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48854 q ha hb
  have h3 (q : Pattern) (ha : d21809 q = 1) (hb : d127410 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21809, d127410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21809, d127410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d127413 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21810 q = 1) (hb : d127414 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21810, d127414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21810, d127414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21811 q = 1) (hb : d127440 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21811, d127440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21811, d127440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21812 q = 1) (hb : d127441 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21812, d127441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21812, d127441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127442 q = 1) (hb : d194420 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127442, d194420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127442, d194420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro49041 (p : Pattern) (ha : d127508 p = 1) (hb : d194427 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22070 q = 1) (hb : d127474 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22070, d127474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48888 q ha hb
    | true =>
      simp only [d22070, d127474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48861 q ha hb
  have h2 (q : Pattern) (ha : d22071 q = 1) (hb : d127475 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22071, d127475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22071, d127475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22072 q = 1) (hb : d127476 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22072, d127476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22072, d127476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22079 q = 1) (hb : d127477 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22079, d127477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48861 q ha hb
    | true =>
      simp only [d22079, d127477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48890 q ha hb
  have h5 (q : Pattern) (ha : d22080 q = 1) (hb : d127478 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22080, d127478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22080, d127478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22081 q = 1) (hb : d127479 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22081, d127479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22081, d127479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22082 q = 1) (hb : d127480 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22082, d127480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22082, d127480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22098 q = 1) (hb : d127494 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22098, d127494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48861 q ha hb
    | true =>
      simp only [d22098, d127494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48862 q ha hb
  have h9 (q : Pattern) (ha : d22099 q = 1) (hb : d127495 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22099, d127495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22099, d127495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22100 q = 1) (hb : d127496 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22100, d127496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22100, d127496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22101 q = 1) (hb : d127497 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22101, d127497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22101, d127497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d127507 q = 1) (hb : d194426 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d127507, d194426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d127507, d194426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d127508 q = 1) (hb : d194427 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d127508, d194427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d127508, d194427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro49042 (p : Pattern) (ha : d127514 p = 1) (hb : d194433 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127509 q = 1) (hb : d194428 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127509, d194428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49041 q ha hb
    | true =>
      simp only [d127509, d194428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127510 q = 1) (hb : d194429 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127510, d194429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127510, d194429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22104 q = 1) (hb : d127500 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22104, d127500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48863 q ha hb
    | true =>
      simp only [d22104, d127500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22105 q = 1) (hb : d127501 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22105, d127501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22105, d127501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127511 q = 1) (hb : d194430 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d127511, d194430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127511, d194430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127512 q = 1) (hb : d194431 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d127512, d194431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127512, d194431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d127513 q = 1) (hb : d194432 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d127513, d194432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127513, d194432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d127514 q = 1) (hb : d194433 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d127514, d194433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127514, d194433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49043 (p : Pattern) (ha : d127538 p = 1) (hb : d194439 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127506 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127519 q = 1) (hb : d194434 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127519, d194434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49042 q ha hb
    | true =>
      simp only [d127519, d194434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48864 q hb ha
  have h3 (q : Pattern) (ha : d127520 q = 1) (hb : d194435 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127520, d194435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127520, d194435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d127534 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d127535 q = 1) (hb : d194436 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127535, d194436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127535, d194436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127536 q = 1) (hb : d194437 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127536, d194437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127536, d194437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127537 q = 1) (hb : d194438 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127537, d194438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127537, d194438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127538 q = 1) (hb : d194439 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127538, d194439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127538, d194439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49044 (p : Pattern) (ha : d127551 p = 1) (hb : d194445 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127327 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21814 q = 1) (hb : d127418 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21814, d127418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49038 q ha hb
    | true =>
      simp only [d21814, d127418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49039 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127436 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d21815 q = 1) (hb : d127437 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21815, d127437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21815, d127437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d127438 q = 1) (hb : d194418 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127438, d194418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d127438, d194418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127439 q = 1) (hb : d194419 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127439, d194419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127439, d194419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127443 q = 1) (hb : d194421 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127443, d194421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d127443, d194421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49040 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d127445 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d127446 q = 1) (hb : d194422 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127446, d194422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127446, d194422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d127447 q = 1) (hb : d194423 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127447, d194423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d127447, d194423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d127448 q = 1) (hb : d194424 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127448, d194424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d127448, d194424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d127449 q = 1) (hb : d194425 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d127449, d194425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127449, d194425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d127539 q = 1) (hb : d194440 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127539, d194440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d127539, d194440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49043 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d127546 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d127547 q = 1) (hb : d194441 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127547, d194441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d127547, d194441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d127548 q = 1) (hb : d194442 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127548, d194442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d127548, d194442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d127549 q = 1) (hb : d194443 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127549, d194443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d127549, d194443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d127550 q = 1) (hb : d194444 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d127550, d194444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d127550, d194444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d127551 q = 1) (hb : d194445 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d127551, d194445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d127551, d194445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro49045 (p : Pattern) (ha : d127557 p = 1) (hb : d194451 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127552 q = 1) (hb : d194446 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d127552, d194446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127552, d194446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49044 q ha hb
  have h2 (q : Pattern) (ha : d127553 q = 1) (hb : d194447 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d127553, d194447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127553, d194447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127554 q = 1) (hb : d194448 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d127554, d194448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127554, d194448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127555 q = 1) (hb : d194449 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d127555, d194449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127555, d194449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127556 q = 1) (hb : d194450 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d127556, d194450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127556, d194450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127557 q = 1) (hb : d194451 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d127557, d194451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127557, d194451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49046 (p : Pattern) (ha : d22281 p = 1) (hb : d127683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127623 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127632 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d127664 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d22276 q = 1) (hb : d127597 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22276, d127597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48907 q ha hb
    | true =>
      simp only [d22276, d127597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48908 q ha hb
  have h5 (q : Pattern) (ha : d22277 q = 1) (hb : d127665 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22277, d127665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22277, d127665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d127679 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d22278 q = 1) (hb : d127680 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22278, d127680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22278, d127680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22279 q = 1) (hb : d127681 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22279, d127681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22279, d127681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d22280 q = 1) (hb : d127682 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22280, d127682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22280, d127682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22281 q = 1) (hb : d127683 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22281, d127683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22281, d127683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro49047 (p : Pattern) (ha : d22291 p = 1) (hb : d127705 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127623 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127632 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127664 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d22276 q = 1) (hb : d127597 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22276, d127597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48907 q ha hb
    | true =>
      simp only [d22276, d127597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48908 q ha hb
  have h4 (q : Pattern) (ha : d22277 q = 1) (hb : d127665 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22277, d127665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22277, d127665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d127679 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d22278 q = 1) (hb : d127680 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22278, d127680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22278, d127680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22279 q = 1) (hb : d127681 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22279, d127681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22279, d127681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22280 q = 1) (hb : d127682 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22280, d127682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22280, d127682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d127689 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d127694 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d127697 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d22286 q = 1) (hb : d127607 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22286, d127607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48910 q ha hb
    | true =>
      simp only [d22286, d127607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48911 q ha hb
  have h13 (q : Pattern) (ha : d22287 q = 1) (hb : d127698 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22287, d127698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22287, d127698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d127701 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d22288 q = 1) (hb : d127702 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22288, d127702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22288, d127702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d22289 q = 1) (hb : d127703 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22289, d127703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22289, d127703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d22290 q = 1) (hb : d127704 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22290, d127704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22290, d127704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d22291 q = 1) (hb : d127705 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22291, d127705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22291, d127705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro49048 (p : Pattern) (ha : d127730 p = 1) (hb : d194457 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127697 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22286 q = 1) (hb : d127607 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22286, d127607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48910 q ha hb
    | true =>
      simp only [d22286, d127607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48911 q ha hb
  have h3 (q : Pattern) (ha : d22287 q = 1) (hb : d127698 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22287, d127698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22287, d127698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d127701 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22288 q = 1) (hb : d127702 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22288, d127702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22288, d127702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22289 q = 1) (hb : d127728 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22289, d127728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22289, d127728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22290 q = 1) (hb : d127729 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22290, d127729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22290, d127729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127730 q = 1) (hb : d194457 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127730, d194457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127730, d194457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro49049 (p : Pattern) (ha : d127801 p = 1) (hb : d194464 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22535 q = 1) (hb : d127767 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22535, d127767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48944 q ha hb
    | true =>
      simp only [d22535, d127767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48918 q ha hb
  have h2 (q : Pattern) (ha : d22536 q = 1) (hb : d127768 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22536, d127768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22536, d127768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22537 q = 1) (hb : d127769 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22537, d127769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22537, d127769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22544 q = 1) (hb : d127770 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22544, d127770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48918 q ha hb
    | true =>
      simp only [d22544, d127770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48946 q ha hb
  have h5 (q : Pattern) (ha : d22545 q = 1) (hb : d127771 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22545, d127771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22545, d127771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22546 q = 1) (hb : d127772 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22546, d127772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22546, d127772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22547 q = 1) (hb : d127773 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22547, d127773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22547, d127773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22563 q = 1) (hb : d127787 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22563, d127787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48918 q ha hb
    | true =>
      simp only [d22563, d127787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48919 q ha hb
  have h9 (q : Pattern) (ha : d22564 q = 1) (hb : d127788 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22564, d127788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22564, d127788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22565 q = 1) (hb : d127789 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22565, d127789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22565, d127789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22566 q = 1) (hb : d127790 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22566, d127790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22566, d127790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d127800 q = 1) (hb : d194463 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d127800, d194463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d127800, d194463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d127801 q = 1) (hb : d194464 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d127801, d194464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d127801, d194464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro49050 (p : Pattern) (ha : d127807 p = 1) (hb : d194470 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127802 q = 1) (hb : d194465 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d127802, d194465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49049 q ha hb
    | true =>
      simp only [d127802, d194465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d127803 q = 1) (hb : d194466 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d127803, d194466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127803, d194466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22569 q = 1) (hb : d127793 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22569, d127793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48920 q ha hb
    | true =>
      simp only [d22569, d127793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22570 q = 1) (hb : d127794 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22570, d127794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22570, d127794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127804 q = 1) (hb : d194467 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d127804, d194467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d127804, d194467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127805 q = 1) (hb : d194468 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d127805, d194468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d127805, d194468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d127806 q = 1) (hb : d194469 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d127806, d194469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127806, d194469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d127807 q = 1) (hb : d194470 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d127807, d194470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127807, d194470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49051 (p : Pattern) (ha : d127831 p = 1) (hb : d194476 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127799 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127812 q = 1) (hb : d194471 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d127812, d194471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49050 q ha hb
    | true =>
      simp only [d127812, d194471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48921 q hb ha
  have h3 (q : Pattern) (ha : d127813 q = 1) (hb : d194472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d127813, d194472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127813, d194472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d127827 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d127828 q = 1) (hb : d194473 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d127828, d194473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127828, d194473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127829 q = 1) (hb : d194474 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d127829, d194474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127829, d194474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127830 q = 1) (hb : d194475 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d127830, d194475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127830, d194475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d127831 q = 1) (hb : d194476 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d127831, d194476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127831, d194476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49052 (p : Pattern) (ha : d127844 p = 1) (hb : d194482 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127615 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22292 q = 1) (hb : d127706 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22292, d127706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49046 q ha hb
    | true =>
      simp only [d22292, d127706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49047 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127724 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d22293 q = 1) (hb : d127725 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d22293, d127725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22293, d127725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d127726 q = 1) (hb : d194455 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127726, d194455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d127726, d194455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d127727 q = 1) (hb : d194456 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127727, d194456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127727, d194456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127731 q = 1) (hb : d194458 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127731, d194458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d127731, d194458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49048 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d127733 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d127734 q = 1) (hb : d194459 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127734, d194459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d127734, d194459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d127735 q = 1) (hb : d194460 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127735, d194460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d127735, d194460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d127736 q = 1) (hb : d194461 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127736, d194461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d127736, d194461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d127737 q = 1) (hb : d194462 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d127737, d194462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127737, d194462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d127832 q = 1) (hb : d194477 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d127832, d194477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d127832, d194477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49051 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d127839 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d127840 q = 1) (hb : d194478 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d127840, d194478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d127840, d194478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d127841 q = 1) (hb : d194479 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d127841, d194479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d127841, d194479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d127842 q = 1) (hb : d194480 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d127842, d194480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d127842, d194480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d127843 q = 1) (hb : d194481 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d127843, d194481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d127843, d194481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d127844 q = 1) (hb : d194482 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d127844, d194482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d127844, d194482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro49053 (p : Pattern) (ha : d127850 p = 1) (hb : d194488 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d127845 q = 1) (hb : d194483 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d127845, d194483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127845, d194483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49052 q ha hb
  have h2 (q : Pattern) (ha : d127846 q = 1) (hb : d194484 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d127846, d194484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127846, d194484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d127847 q = 1) (hb : d194485 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d127847, d194485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127847, d194485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127848 q = 1) (hb : d194486 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d127848, d194486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127848, d194486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d127849 q = 1) (hb : d194487 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d127849, d194487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127849, d194487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127850 q = 1) (hb : d194488 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d127850, d194488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d127850, d194488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49054 (p : Pattern) (ha : d22736 p = 1) (hb : d127976 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127917 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127926 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d127957 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d22731 q = 1) (hb : d127891 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22731, d127891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48962 q ha hb
    | true =>
      simp only [d22731, d127891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48963 q ha hb
  have h5 (q : Pattern) (ha : d22732 q = 1) (hb : d127958 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22732, d127958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22732, d127958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d127972 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d22733 q = 1) (hb : d127973 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22733, d127973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22733, d127973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22734 q = 1) (hb : d127974 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22734, d127974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22734, d127974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d22735 q = 1) (hb : d127975 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22735, d127975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22735, d127975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22736 q = 1) (hb : d127976 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22736, d127976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22736, d127976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro49055 (p : Pattern) (ha : d22746 p = 1) (hb : d127998 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127917 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127926 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d127957 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d22731 q = 1) (hb : d127891 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22731, d127891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48962 q ha hb
    | true =>
      simp only [d22731, d127891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48963 q ha hb
  have h4 (q : Pattern) (ha : d22732 q = 1) (hb : d127958 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22732, d127958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22732, d127958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d127972 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d22733 q = 1) (hb : d127973 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22733, d127973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22733, d127973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22734 q = 1) (hb : d127974 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22734, d127974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22734, d127974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22735 q = 1) (hb : d127975 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22735, d127975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22735, d127975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d127982 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d127987 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d127990 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d22741 q = 1) (hb : d127901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22741, d127901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48965 q ha hb
    | true =>
      simp only [d22741, d127901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48966 q ha hb
  have h13 (q : Pattern) (ha : d22742 q = 1) (hb : d127991 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22742, d127991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22742, d127991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d127994 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d22743 q = 1) (hb : d127995 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22743, d127995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22743, d127995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d22744 q = 1) (hb : d127996 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22744, d127996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22744, d127996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d22745 q = 1) (hb : d127997 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22745, d127997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22745, d127997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d22746 q = 1) (hb : d127998 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22746, d127998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22746, d127998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro49056 (p : Pattern) (ha : d128023 p = 1) (hb : d194495 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d127990 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d22741 q = 1) (hb : d127901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d22741, d127901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48965 q ha hb
    | true =>
      simp only [d22741, d127901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48966 q ha hb
  have h3 (q : Pattern) (ha : d22742 q = 1) (hb : d127991 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22742, d127991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22742, d127991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d127994 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22743 q = 1) (hb : d127995 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22743, d127995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22743, d127995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22744 q = 1) (hb : d128021 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22744, d128021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22744, d128021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22745 q = 1) (hb : d128022 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22745, d128022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22745, d128022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128023 q = 1) (hb : d194495 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128023, d194495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128023, d194495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro49057 (p : Pattern) (ha : d128093 p = 1) (hb : d194502 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22949 q = 1) (hb : d128059 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22949, d128059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48999 q ha hb
    | true =>
      simp only [d22949, d128059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48973 q ha hb
  have h2 (q : Pattern) (ha : d22950 q = 1) (hb : d128060 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22950, d128060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22950, d128060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22951 q = 1) (hb : d128061 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22951, d128061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22951, d128061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22958 q = 1) (hb : d128062 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22958, d128062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48973 q ha hb
    | true =>
      simp only [d22958, d128062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49001 q ha hb
  have h5 (q : Pattern) (ha : d22959 q = 1) (hb : d128063 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22959, d128063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22959, d128063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22960 q = 1) (hb : d128064 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22960, d128064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22960, d128064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22961 q = 1) (hb : d128065 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22961, d128065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22961, d128065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22977 q = 1) (hb : d128079 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d22977, d128079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48973 q ha hb
    | true =>
      simp only [d22977, d128079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48974 q ha hb
  have h9 (q : Pattern) (ha : d22978 q = 1) (hb : d128080 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d22978, d128080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22978, d128080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22979 q = 1) (hb : d128081 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d22979, d128081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22979, d128081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d22980 q = 1) (hb : d128082 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d22980, d128082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22980, d128082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128092 q = 1) (hb : d194501 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d128092, d194501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d128092, d194501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d128093 q = 1) (hb : d194502 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d128093, d194502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128093, d194502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro49058 (p : Pattern) (ha : d128099 p = 1) (hb : d194508 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128094 q = 1) (hb : d194503 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d128094, d194503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49057 q ha hb
    | true =>
      simp only [d128094, d194503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128095 q = 1) (hb : d194504 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d128095, d194504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128095, d194504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d22983 q = 1) (hb : d128085 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d22983, d128085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48975 q ha hb
    | true =>
      simp only [d22983, d128085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d22984 q = 1) (hb : d128086 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d22984, d128086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22984, d128086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128096 q = 1) (hb : d194505 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d128096, d194505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128096, d194505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128097 q = 1) (hb : d194506 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d128097, d194506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128097, d194506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d128098 q = 1) (hb : d194507 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d128098, d194507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128098, d194507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d128099 q = 1) (hb : d194508 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d128099, d194508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128099, d194508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro49059 (p : Pattern) (ha : d128123 p = 1) (hb : d194514 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d128091 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128104 q = 1) (hb : d194509 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d128104, d194509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49058 q ha hb
    | true =>
      simp only [d128104, d194509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro48976 q hb ha
  have h3 (q : Pattern) (ha : d128105 q = 1) (hb : d194510 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128105, d194510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128105, d194510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d128119 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128120 q = 1) (hb : d194511 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128120, d194511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128120, d194511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128121 q = 1) (hb : d194512 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128121, d194512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128121, d194512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128122 q = 1) (hb : d194513 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128122, d194513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128122, d194513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128123 q = 1) (hb : d194514 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128123, d194514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128123, d194514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49060 (p : Pattern) (ha : d128136 p = 1) (hb : d194520 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d127909 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22747 q = 1) (hb : d127999 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22747, d127999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49054 q ha hb
    | true =>
      simp only [d22747, d127999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49055 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d128017 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d22748 q = 1) (hb : d128018 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d22748, d128018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22748, d128018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128019 q = 1) (hb : d194493 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128019, d194493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128019, d194493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128020 q = 1) (hb : d194494 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128020, d194494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128020, d194494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128024 q = 1) (hb : d194496 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128024, d194496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d128024, d194496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49056 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d128026 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d128027 q = 1) (hb : d194497 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128027, d194497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128027, d194497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d128028 q = 1) (hb : d194498 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128028, d194498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128028, d194498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d128029 q = 1) (hb : d194499 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128029, d194499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128029, d194499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d128030 q = 1) (hb : d194500 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128030, d194500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128030, d194500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128124 q = 1) (hb : d194515 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128124, d194515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d128124, d194515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49059 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d128131 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d128132 q = 1) (hb : d194516 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128132, d194516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128132, d194516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d128133 q = 1) (hb : d194517 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128133, d194517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128133, d194517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d128134 q = 1) (hb : d194518 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128134, d194518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128134, d194518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d128135 q = 1) (hb : d194519 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128135, d194519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128135, d194519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d128136 q = 1) (hb : d194520 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128136, d194520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128136, d194520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro49061 (p : Pattern) (ha : d128142 p = 1) (hb : d194526 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128137 q = 1) (hb : d194521 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128137, d194521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128137, d194521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49060 q ha hb
  have h2 (q : Pattern) (ha : d128138 q = 1) (hb : d194522 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128138, d194522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128138, d194522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128139 q = 1) (hb : d194523 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128139, d194523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128139, d194523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128140 q = 1) (hb : d194524 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128140, d194524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128140, d194524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128141 q = 1) (hb : d194525 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128141, d194525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128141, d194525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128142 q = 1) (hb : d194526 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128142, d194526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128142, d194526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49062 (p : Pattern) (ha : d128148 p = 1) (hb : d194532 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d127103 q = 1) (hb : d194389 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d127103, d194389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49025 q ha hb
    | true =>
      simp only [d127103, d194389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49031 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d127274 q = 1) (hb : d194416 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d127274, d194416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127274, d194416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49037 q ha hb
  have h3 (q : Pattern) (ha : d127275 q = 1) (hb : d194417 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d127275, d194417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d127275, d194417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d127558 q = 1) (hb : d194452 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d127558, d194452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127558, d194452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49045 q ha hb
  have h5 (q : Pattern) (ha : d127559 q = 1) (hb : d194453 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d127559, d194453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127559, d194453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d127560 q = 1) (hb : d194454 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d127560, d194454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d127560, d194454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d127851 q = 1) (hb : d194489 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d127851, d194489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127851, d194489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49053 q ha hb
  have h8 (q : Pattern) (ha : d127852 q = 1) (hb : d194490 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d127852, d194490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127852, d194490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d127853 q = 1) (hb : d194491 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d127853, d194491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d127853, d194491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d127854 q = 1) (hb : d194492 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d127854, d194492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d127854, d194492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128143 q = 1) (hb : d194527 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128143, d194527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128143, d194527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49061 q ha hb
  have h12 (q : Pattern) (ha : d128144 q = 1) (hb : d194528 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128144, d194528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128144, d194528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128145 q = 1) (hb : d194529 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128145, d194529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128145, d194529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128146 q = 1) (hb : d194530 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d128146, d194530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128146, d194530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128147 q = 1) (hb : d194531 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d128147, d194531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128147, d194531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128148 q = 1) (hb : d194532 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d128148, d194532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128148, d194532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro49063 (p : Pattern) (ha : d128154 p = 1) (hb : d194538 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128149 q = 1) (hb : d194533 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d128149, d194533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49062 q ha hb
    | true =>
      simp only [d128149, d194533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128150 q = 1) (hb : d194534 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d128150, d194534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128150, d194534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128151 q = 1) (hb : d194535 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d128151, d194535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128151, d194535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128152 q = 1) (hb : d194536 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d128152, d194536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128152, d194536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128153 q = 1) (hb : d194537 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d128153, d194537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128153, d194537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128154 q = 1) (hb : d194538 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d128154, d194538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128154, d194538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49064 (p : Pattern) (ha : d128160 p = 1) (hb : d194544 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128155 q = 1) (hb : d194539 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d128155, d194539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49063 q ha hb
    | true =>
      simp only [d128155, d194539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128156 q = 1) (hb : d194540 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d128156, d194540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128156, d194540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128157 q = 1) (hb : d194541 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d128157, d194541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128157, d194541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128158 q = 1) (hb : d194542 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d128158, d194542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128158, d194542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128159 q = 1) (hb : d194543 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d128159, d194543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128159, d194543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128160 q = 1) (hb : d194544 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d128160, d194544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128160, d194544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49065 (p : Pattern) (ha : d128166 p = 1) (hb : d194550 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128161 q = 1) (hb : d194545 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d128161, d194545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49064 q ha hb
    | true =>
      simp only [d128161, d194545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128162 q = 1) (hb : d194546 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d128162, d194546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128162, d194546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128163 q = 1) (hb : d194547 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d128163, d194547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128163, d194547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128164 q = 1) (hb : d194548 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d128164, d194548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128164, d194548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128165 q = 1) (hb : d194549 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d128165, d194549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128165, d194549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128166 q = 1) (hb : d194550 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d128166, d194550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128166, d194550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49066 (p : Pattern) (ha : d128172 p = 1) (hb : d194556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128167 q = 1) (hb : d194551 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d128167, d194551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49065 q ha hb
    | true =>
      simp only [d128167, d194551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128168 q = 1) (hb : d194552 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d128168, d194552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128168, d194552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128169 q = 1) (hb : d194553 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d128169, d194553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128169, d194553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128170 q = 1) (hb : d194554 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d128170, d194554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128170, d194554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128171 q = 1) (hb : d194555 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d128171, d194555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128171, d194555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128172 q = 1) (hb : d194556 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d128172, d194556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128172, d194556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49067 (p : Pattern) (ha : d128178 p = 1) (hb : d194562 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128173 q = 1) (hb : d194557 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d128173, d194557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49066 q ha hb
    | true =>
      simp only [d128173, d194557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128174 q = 1) (hb : d194558 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d128174, d194558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128174, d194558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128175 q = 1) (hb : d194559 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d128175, d194559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128175, d194559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128176 q = 1) (hb : d194560 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d128176, d194560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128176, d194560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128177 q = 1) (hb : d194561 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d128177, d194561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128177, d194561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128178 q = 1) (hb : d194562 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d128178, d194562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128178, d194562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49068 (p : Pattern) (ha : d128184 p = 1) (hb : d194568 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128179 q = 1) (hb : d194563 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d128179, d194563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49067 q ha hb
    | true =>
      simp only [d128179, d194563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128180 q = 1) (hb : d194564 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d128180, d194564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128180, d194564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128181 q = 1) (hb : d194565 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d128181, d194565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128181, d194565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128182 q = 1) (hb : d194566 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d128182, d194566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128182, d194566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128183 q = 1) (hb : d194567 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d128183, d194567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128183, d194567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128184 q = 1) (hb : d194568 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d128184, d194568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128184, d194568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49069 (p : Pattern) (ha : d128190 p = 1) (hb : d194574 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128185 q = 1) (hb : d194569 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d128185, d194569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49068 q ha hb
    | true =>
      simp only [d128185, d194569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d128186 q = 1) (hb : d194570 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d128186, d194570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128186, d194570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d128187 q = 1) (hb : d194571 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d128187, d194571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128187, d194571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d128188 q = 1) (hb : d194572 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d128188, d194572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128188, d194572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d128189 q = 1) (hb : d194573 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d128189, d194573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128189, d194573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d128190 q = 1) (hb : d194574 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d128190, d194574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128190, d194574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro49070 (p : Pattern) (ha : d20966 p = 1) (hb : d128195 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d300 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d306 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d15979 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20906 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d20962 q = 1) (hb : d128191 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20962, d128191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20962, d128191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d5350 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d20963 q = 1) (hb : d128192 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20963, d128192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20963, d128192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20964 q = 1) (hb : d128193 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20964, d128193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20964, d128193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20965 q = 1) (hb : d128194 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20965, d128194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20965, d128194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20966 q = 1) (hb : d128195 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20966, d128195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20966, d128195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro49071 (p : Pattern) (ha : d20973 p = 1) (hb : d128200 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d300 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d306 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d15979 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d20906 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20962 q = 1) (hb : d128191 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20962, d128191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20962, d128191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d5350 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d20963 q = 1) (hb : d128192 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20963, d128192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20963, d128192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20964 q = 1) (hb : d128193 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20964, d128193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20964, d128193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20965 q = 1) (hb : d128194 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20965, d128194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20965, d128194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d380 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d384 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d15986 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d20913 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d20969 q = 1) (hb : d128196 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20969, d128196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d20969, d128196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d5357 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d20970 q = 1) (hb : d128197 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20970, d128197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d20970, d128197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d20971 q = 1) (hb : d128198 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20971, d128198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d20971, d128198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d20972 q = 1) (hb : d128199 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20972, d128199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20972, d128199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d20973 q = 1) (hb : d128200 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20973, d128200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20973, d128200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro49072 (p : Pattern) (ha : d128207 p = 1) (hb : d194340 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15986 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d20913 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d20969 q = 1) (hb : d128196 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20969, d128196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20969, d128196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5357 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d20970 q = 1) (hb : d128197 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20970, d128197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20970, d128197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20971 q = 1) (hb : d128205 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20971, d128205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20971, d128205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20972 q = 1) (hb : d128206 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20972, d128206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20972, d128206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128207 q = 1) (hb : d194340 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128207, d194340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128207, d194340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro49073 (p : Pattern) (ha : d128217 p = 1) (hb : d194350 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16017 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d20945 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128213 q = 1) (hb : d194346 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128213, d194346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128213, d194346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5379 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128214 q = 1) (hb : d194347 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128214, d194347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128214, d194347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128215 q = 1) (hb : d194348 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128215, d194348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128215, d194348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128216 q = 1) (hb : d194349 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128216, d194349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128216, d194349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128217 q = 1) (hb : d194350 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128217, d194350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128217, d194350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49074 (p : Pattern) (ha : d128223 p = 1) (hb : d194356 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d294 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20974 q = 1) (hb : d128201 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20974, d128201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49070 q ha hb
    | true =>
      simp only [d20974, d128201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49071 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d398 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d20975 q = 1) (hb : d128202 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20975, d128202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20975, d128202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128203 q = 1) (hb : d194338 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128203, d194338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128203, d194338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128204 q = 1) (hb : d194339 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128204, d194339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128204, d194339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128208 q = 1) (hb : d194341 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128208, d194341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128208, d194341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49072 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d407 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d128209 q = 1) (hb : d194342 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128209, d194342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128209, d194342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d128210 q = 1) (hb : d194343 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128210, d194343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128210, d194343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d128211 q = 1) (hb : d194344 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128211, d194344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128211, d194344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d128212 q = 1) (hb : d194345 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128212, d194345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128212, d194345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128218 q = 1) (hb : d194351 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128218, d194351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128218, d194351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49073 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d463 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d128219 q = 1) (hb : d194352 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128219, d194352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128219, d194352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d128220 q = 1) (hb : d194353 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128220, d194353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128220, d194353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d128221 q = 1) (hb : d194354 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128221, d194354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128221, d194354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d128222 q = 1) (hb : d194355 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128222, d194355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128222, d194355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d128223 q = 1) (hb : d194356 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128223, d194356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128223, d194356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro49075 (p : Pattern) (ha : d128229 p = 1) (hb : d194362 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d99 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51653 q = 1) (hb : d53648 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51653, d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51653, d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro376 q ha hb
  have h3 (q : Pattern) (ha : d51654 q = 1) (hb : d53649 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51654, d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51654, d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51655 q = 1) (hb : d53650 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51655, d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51655, d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51656 q = 1) (hb : d53651 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51656, d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51656, d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51657 q = 1) (hb : d53652 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51657, d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d51657, d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128224 q = 1) (hb : d194357 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128224, d194357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128224, d194357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49074 q ha hb
  have h8 (q : Pattern) (ha : d128225 q = 1) (hb : d194358 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128225, d194358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128225, d194358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128226 q = 1) (hb : d194359 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128226, d194359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128226, d194359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128227 q = 1) (hb : d194360 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128227, d194360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128227, d194360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128228 q = 1) (hb : d194361 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128228, d194361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128228, d194361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d128229 q = 1) (hb : d194362 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128229, d194362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128229, d194362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro49076 (p : Pattern) (ha : d21151 p = 1) (hb : d128234 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16066 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16072 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d16094 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21146 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21147 q = 1) (hb : d128230 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21147, d128230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21147, d128230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d16116 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d21148 q = 1) (hb : d128231 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21148, d128231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21148, d128231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21149 q = 1) (hb : d128232 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21149, d128232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21149, d128232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21150 q = 1) (hb : d128233 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21150, d128233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21150, d128233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21151 q = 1) (hb : d128234 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21151, d128234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21151, d128234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro49077 (p : Pattern) (ha : d21161 p = 1) (hb : d128239 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d16066 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16072 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16094 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d21146 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d21147 q = 1) (hb : d128230 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21147, d128230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21147, d128230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d16116 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d21148 q = 1) (hb : d128231 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21148, d128231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21148, d128231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21149 q = 1) (hb : d128232 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21149, d128232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21149, d128232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21150 q = 1) (hb : d128233 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21150, d128233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21150, d128233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d16125 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d16129 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d16131 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d21156 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d21157 q = 1) (hb : d128235 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21157, d128235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21157, d128235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d16137 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d21158 q = 1) (hb : d128236 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21158, d128236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21158, d128236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d21159 q = 1) (hb : d128237 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21159, d128237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21159, d128237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21160 q = 1) (hb : d128238 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21160, d128238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21160, d128238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d21161 q = 1) (hb : d128239 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21161, d128239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21161, d128239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro49078 (p : Pattern) (ha : d128246 p = 1) (hb : d194365 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16131 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21156 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d21157 q = 1) (hb : d128235 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21157, d128235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21157, d128235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d16137 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21158 q = 1) (hb : d128236 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21158, d128236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21158, d128236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21159 q = 1) (hb : d128244 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21159, d128244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21159, d128244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21160 q = 1) (hb : d128245 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21160, d128245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21160, d128245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128246 q = 1) (hb : d194365 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128246, d194365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128246, d194365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro49079 (p : Pattern) (ha : d128256 p = 1) (hb : d194376 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16187 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d194371 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128252 q = 1) (hb : d194372 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128252, d194372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128252, d194372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d16209 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128253 q = 1) (hb : d194373 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128253, d194373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128253, d194373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128254 q = 1) (hb : d194374 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128254, d194374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128254, d194374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128255 q = 1) (hb : d194375 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128255, d194375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128255, d194375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128256 q = 1) (hb : d194376 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128256, d194376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128256, d194376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49080 (p : Pattern) (ha : d128262 p = 1) (hb : d194382 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d16060 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21162 q = 1) (hb : d128240 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21162, d128240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49076 q ha hb
    | true =>
      simp only [d21162, d128240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49077 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16144 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d21163 q = 1) (hb : d128241 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21163, d128241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21163, d128241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128242 q = 1) (hb : d194363 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128242, d194363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128242, d194363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128243 q = 1) (hb : d194364 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128243, d194364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128243, d194364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128247 q = 1) (hb : d194366 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128247, d194366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128247, d194366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49078 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d654 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d128248 q = 1) (hb : d194367 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128248, d194367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128248, d194367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d128249 q = 1) (hb : d194368 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128249, d194368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128249, d194368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d128250 q = 1) (hb : d194369 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128250, d194369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128250, d194369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d128251 q = 1) (hb : d194370 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128251, d194370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128251, d194370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128257 q = 1) (hb : d194377 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128257, d194377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128257, d194377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49079 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d737 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d128258 q = 1) (hb : d194378 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128258, d194378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128258, d194378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d128259 q = 1) (hb : d194379 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128259, d194379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128259, d194379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d128260 q = 1) (hb : d194380 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128260, d194380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128260, d194380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d128261 q = 1) (hb : d194381 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128261, d194381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128261, d194381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d128262 q = 1) (hb : d194382 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128262, d194382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128262, d194382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro49081 (p : Pattern) (ha : d128268 p = 1) (hb : d194388 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128263 q = 1) (hb : d194383 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128263, d194383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128263, d194383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49080 q ha hb
  have h2 (q : Pattern) (ha : d128264 q = 1) (hb : d194384 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128264, d194384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128264, d194384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128265 q = 1) (hb : d194385 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128265, d194385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128265, d194385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128266 q = 1) (hb : d194386 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128266, d194386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128266, d194386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128267 q = 1) (hb : d194387 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128267, d194387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128267, d194387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128268 q = 1) (hb : d194388 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128268, d194388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128268, d194388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49082 (p : Pattern) (ha : d21450 p = 1) (hb : d128274 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16263 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16269 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d16291 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21445 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21446 q = 1) (hb : d128270 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21446, d128270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21446, d128270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d16316 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d21447 q = 1) (hb : d128271 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21447, d128271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21447, d128271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21448 q = 1) (hb : d128272 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21448, d128272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21448, d128272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21449 q = 1) (hb : d128273 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21449, d128273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21449, d128273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21450 q = 1) (hb : d128274 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21450, d128274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21450, d128274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro49083 (p : Pattern) (ha : d21460 p = 1) (hb : d128279 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d16263 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16269 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16291 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d21445 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d21446 q = 1) (hb : d128270 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21446, d128270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21446, d128270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d16316 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d21447 q = 1) (hb : d128271 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21447, d128271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21447, d128271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21448 q = 1) (hb : d128272 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21448, d128272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21448, d128272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21449 q = 1) (hb : d128273 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21449, d128273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21449, d128273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d16325 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d16329 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d16331 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d21455 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d21456 q = 1) (hb : d128275 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21456, d128275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21456, d128275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d16337 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d21457 q = 1) (hb : d128276 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21457, d128276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21457, d128276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d21458 q = 1) (hb : d128277 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21458, d128277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21458, d128277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21459 q = 1) (hb : d128278 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21459, d128278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21459, d128278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d21460 q = 1) (hb : d128279 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21460, d128279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21460, d128279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro49084 (p : Pattern) (ha : d128286 p = 1) (hb : d194392 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16331 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21455 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d21456 q = 1) (hb : d128275 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21456, d128275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21456, d128275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d16337 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21457 q = 1) (hb : d128276 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21457, d128276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21457, d128276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21458 q = 1) (hb : d128284 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21458, d128284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21458, d128284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21459 q = 1) (hb : d128285 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21459, d128285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21459, d128285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128286 q = 1) (hb : d194392 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128286, d194392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128286, d194392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro49085 (p : Pattern) (ha : d128296 p = 1) (hb : d194403 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16392 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d194398 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128292 q = 1) (hb : d194399 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128292, d194399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128292, d194399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d16419 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128293 q = 1) (hb : d194400 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128293, d194400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128293, d194400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128294 q = 1) (hb : d194401 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128294, d194401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128294, d194401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128295 q = 1) (hb : d194402 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128295, d194402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128295, d194402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128296 q = 1) (hb : d194403 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128296, d194403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128296, d194403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49086 (p : Pattern) (ha : d128302 p = 1) (hb : d194409 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d16257 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21461 q = 1) (hb : d128280 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21461, d128280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49082 q ha hb
    | true =>
      simp only [d21461, d128280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49083 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16344 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d21462 q = 1) (hb : d128281 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21462, d128281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21462, d128281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128282 q = 1) (hb : d194390 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128282, d194390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128282, d194390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128283 q = 1) (hb : d194391 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128283, d194391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128283, d194391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128287 q = 1) (hb : d194393 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128287, d194393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128287, d194393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49084 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d960 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d128288 q = 1) (hb : d194394 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128288, d194394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128288, d194394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d128289 q = 1) (hb : d194395 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128289, d194395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128289, d194395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d128290 q = 1) (hb : d194396 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128290, d194396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128290, d194396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d128291 q = 1) (hb : d194397 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128291, d194397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128291, d194397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128297 q = 1) (hb : d194404 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128297, d194404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128297, d194404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49085 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d1070 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d128298 q = 1) (hb : d194405 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128298, d194405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128298, d194405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d128299 q = 1) (hb : d194406 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128299, d194406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128299, d194406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d128300 q = 1) (hb : d194407 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128300, d194407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128300, d194407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d128301 q = 1) (hb : d194408 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128301, d194408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128301, d194408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d128302 q = 1) (hb : d194409 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128302, d194409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128302, d194409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro49087 (p : Pattern) (ha : d128308 p = 1) (hb : d194415 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128303 q = 1) (hb : d194410 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128303, d194410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128303, d194410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49086 q ha hb
  have h2 (q : Pattern) (ha : d128304 q = 1) (hb : d194411 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128304, d194411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128304, d194411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128305 q = 1) (hb : d194412 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128305, d194412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128305, d194412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128306 q = 1) (hb : d194413 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128306, d194413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128306, d194413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128307 q = 1) (hb : d194414 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128307, d194414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128307, d194414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128308 q = 1) (hb : d194415 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128308, d194415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128308, d194415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49088 (p : Pattern) (ha : d21803 p = 1) (hb : d128315 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16497 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16506 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d16538 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21798 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21799 q = 1) (hb : d128311 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21799, d128311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21799, d128311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d16587 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d21800 q = 1) (hb : d128312 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21800, d128312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21800, d128312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21801 q = 1) (hb : d128313 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21801, d128313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21801, d128313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21802 q = 1) (hb : d128314 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21802, d128314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21802, d128314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21803 q = 1) (hb : d128315 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21803, d128315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21803, d128315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro49089 (p : Pattern) (ha : d21813 p = 1) (hb : d128320 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d16497 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16506 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16538 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d21798 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d21799 q = 1) (hb : d128311 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21799, d128311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21799, d128311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d16587 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d21800 q = 1) (hb : d128312 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21800, d128312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21800, d128312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21801 q = 1) (hb : d128313 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21801, d128313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21801, d128313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21802 q = 1) (hb : d128314 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21802, d128314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21802, d128314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d16597 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d16602 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d16605 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d21808 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d21809 q = 1) (hb : d128316 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21809, d128316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21809, d128316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d16612 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d21810 q = 1) (hb : d128317 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21810, d128317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d21810, d128317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d21811 q = 1) (hb : d128318 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21811, d128318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21811, d128318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21812 q = 1) (hb : d128319 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21812, d128319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21812, d128319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d21813 q = 1) (hb : d128320 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21813, d128320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21813, d128320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro49090 (p : Pattern) (ha : d128327 p = 1) (hb : d194420 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16605 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d21808 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d21809 q = 1) (hb : d128316 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21809, d128316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21809, d128316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d16612 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21810 q = 1) (hb : d128317 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21810, d128317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21810, d128317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21811 q = 1) (hb : d128325 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21811, d128325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21811, d128325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21812 q = 1) (hb : d128326 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21812, d128326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21812, d128326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128327 q = 1) (hb : d194420 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128327, d194420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128327, d194420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro49091 (p : Pattern) (ha : d128337 p = 1) (hb : d194439 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16705 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d194434 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128333 q = 1) (hb : d194435 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128333, d194435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128333, d194435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d16756 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128334 q = 1) (hb : d194436 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128334, d194436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128334, d194436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128335 q = 1) (hb : d194437 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128335, d194437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128335, d194437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128336 q = 1) (hb : d194438 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128336, d194438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128336, d194438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128337 q = 1) (hb : d194439 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128337, d194439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128337, d194439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49092 (p : Pattern) (ha : d128343 p = 1) (hb : d194445 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d16489 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21814 q = 1) (hb : d128321 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21814, d128321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49088 q ha hb
    | true =>
      simp only [d21814, d128321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49089 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16635 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d21815 q = 1) (hb : d128322 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21815, d128322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21815, d128322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128323 q = 1) (hb : d194418 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128323, d194418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128323, d194418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128324 q = 1) (hb : d194419 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128324, d194419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128324, d194419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128328 q = 1) (hb : d194421 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128328, d194421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128328, d194421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49090 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d16644 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d128329 q = 1) (hb : d194422 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128329, d194422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128329, d194422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d128330 q = 1) (hb : d194423 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128330, d194423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128330, d194423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d128331 q = 1) (hb : d194424 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128331, d194424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128331, d194424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d128332 q = 1) (hb : d194425 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128332, d194425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128332, d194425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128338 q = 1) (hb : d194440 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128338, d194440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128338, d194440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49091 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d16772 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d128339 q = 1) (hb : d194441 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128339, d194441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128339, d194441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d128340 q = 1) (hb : d194442 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128340, d194442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128340, d194442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d128341 q = 1) (hb : d194443 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128341, d194443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128341, d194443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d128342 q = 1) (hb : d194444 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128342, d194444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128342, d194444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d128343 q = 1) (hb : d194445 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128343, d194445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128343, d194445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro49093 (p : Pattern) (ha : d128349 p = 1) (hb : d194451 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128344 q = 1) (hb : d194446 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128344, d194446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128344, d194446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49092 q ha hb
  have h2 (q : Pattern) (ha : d128345 q = 1) (hb : d194447 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128345, d194447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128345, d194447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128346 q = 1) (hb : d194448 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128346, d194448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128346, d194448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128347 q = 1) (hb : d194449 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128347, d194449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128347, d194449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128348 q = 1) (hb : d194450 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128348, d194450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128348, d194450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128349 q = 1) (hb : d194451 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128349, d194451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128349, d194451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49094 (p : Pattern) (ha : d22281 p = 1) (hb : d128357 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16849 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16858 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d16890 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22276 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22277 q = 1) (hb : d128353 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22277, d128353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22277, d128353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d16942 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d22278 q = 1) (hb : d128354 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22278, d128354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22278, d128354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22279 q = 1) (hb : d128355 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22279, d128355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22279, d128355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d22280 q = 1) (hb : d128356 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22280, d128356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22280, d128356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22281 q = 1) (hb : d128357 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22281, d128357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22281, d128357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro49095 (p : Pattern) (ha : d22291 p = 1) (hb : d128362 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d16849 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16858 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16890 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d22276 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d22277 q = 1) (hb : d128353 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22277, d128353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22277, d128353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d16942 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d22278 q = 1) (hb : d128354 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22278, d128354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22278, d128354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22279 q = 1) (hb : d128355 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22279, d128355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22279, d128355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22280 q = 1) (hb : d128356 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22280, d128356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22280, d128356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d16952 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d16957 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d16960 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d22286 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d22287 q = 1) (hb : d128358 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22287, d128358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22287, d128358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d16967 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d22288 q = 1) (hb : d128359 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22288, d128359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22288, d128359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d22289 q = 1) (hb : d128360 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22289, d128360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22289, d128360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d22290 q = 1) (hb : d128361 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22290, d128361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22290, d128361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d22291 q = 1) (hb : d128362 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22291, d128362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22291, d128362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro49096 (p : Pattern) (ha : d128369 p = 1) (hb : d194457 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16960 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d22286 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d22287 q = 1) (hb : d128358 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22287, d128358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22287, d128358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d16967 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22288 q = 1) (hb : d128359 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22288, d128359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22288, d128359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22289 q = 1) (hb : d128367 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22289, d128367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22289, d128367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22290 q = 1) (hb : d128368 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22290, d128368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22290, d128368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128369 q = 1) (hb : d194457 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128369, d194457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128369, d194457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro49097 (p : Pattern) (ha : d128379 p = 1) (hb : d194476 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17065 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d194471 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128375 q = 1) (hb : d194472 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128375, d194472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128375, d194472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d17121 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128376 q = 1) (hb : d194473 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128376, d194473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128376, d194473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128377 q = 1) (hb : d194474 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128377, d194474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128377, d194474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128378 q = 1) (hb : d194475 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128378, d194475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128378, d194475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128379 q = 1) (hb : d194476 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128379, d194476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128379, d194476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49098 (p : Pattern) (ha : d128385 p = 1) (hb : d194482 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d16841 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22292 q = 1) (hb : d128363 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22292, d128363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49094 q ha hb
    | true =>
      simp only [d22292, d128363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49095 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16990 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d22293 q = 1) (hb : d128364 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d22293, d128364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22293, d128364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128365 q = 1) (hb : d194455 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128365, d194455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128365, d194455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128366 q = 1) (hb : d194456 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128366, d194456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128366, d194456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128370 q = 1) (hb : d194458 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128370, d194458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128370, d194458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49096 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d16999 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d128371 q = 1) (hb : d194459 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128371, d194459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128371, d194459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d128372 q = 1) (hb : d194460 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128372, d194460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128372, d194460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d128373 q = 1) (hb : d194461 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128373, d194461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128373, d194461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d128374 q = 1) (hb : d194462 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128374, d194462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128374, d194462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128380 q = 1) (hb : d194477 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128380, d194477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128380, d194477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49097 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d17137 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d128381 q = 1) (hb : d194478 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128381, d194478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128381, d194478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d128382 q = 1) (hb : d194479 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128382, d194479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128382, d194479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d128383 q = 1) (hb : d194480 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128383, d194480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128383, d194480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d128384 q = 1) (hb : d194481 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128384, d194481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128384, d194481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d128385 q = 1) (hb : d194482 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128385, d194482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128385, d194482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro49099 (p : Pattern) (ha : d128391 p = 1) (hb : d194488 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128386 q = 1) (hb : d194483 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128386, d194483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128386, d194483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49098 q ha hb
  have h2 (q : Pattern) (ha : d128387 q = 1) (hb : d194484 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128387, d194484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128387, d194484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128388 q = 1) (hb : d194485 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128388, d194485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128388, d194485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128389 q = 1) (hb : d194486 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128389, d194486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128389, d194486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128390 q = 1) (hb : d194487 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128390, d194487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128390, d194487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128391 q = 1) (hb : d194488 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128391, d194488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128391, d194488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49100 (p : Pattern) (ha : d22736 p = 1) (hb : d128400 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17215 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d17224 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d17255 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d22731 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22732 q = 1) (hb : d128396 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22732, d128396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22732, d128396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d17307 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d22733 q = 1) (hb : d128397 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22733, d128397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22733, d128397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22734 q = 1) (hb : d128398 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22734, d128398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22734, d128398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d22735 q = 1) (hb : d128399 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22735, d128399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22735, d128399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22736 q = 1) (hb : d128400 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22736, d128400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22736, d128400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro49101 (p : Pattern) (ha : d22746 p = 1) (hb : d128405 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d17215 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17224 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d17255 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d22731 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d22732 q = 1) (hb : d128396 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22732, d128396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22732, d128396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d17307 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d22733 q = 1) (hb : d128397 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22733, d128397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22733, d128397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22734 q = 1) (hb : d128398 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22734, d128398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22734, d128398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d22735 q = 1) (hb : d128399 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22735, d128399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22735, d128399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d17317 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d17322 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d17325 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d22741 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d22742 q = 1) (hb : d128401 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22742, d128401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22742, d128401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d17332 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d22743 q = 1) (hb : d128402 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22743, d128402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22743, d128402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d22744 q = 1) (hb : d128403 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22744, d128403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22744, d128403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d22745 q = 1) (hb : d128404 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22745, d128404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22745, d128404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d22746 q = 1) (hb : d128405 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d22746, d128405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d22746, d128405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro49102 (p : Pattern) (ha : d128412 p = 1) (hb : d194495 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17325 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d22741 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d22742 q = 1) (hb : d128401 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d22742, d128401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22742, d128401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d17332 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d22743 q = 1) (hb : d128402 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d22743, d128402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22743, d128402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22744 q = 1) (hb : d128410 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d22744, d128410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22744, d128410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d22745 q = 1) (hb : d128411 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d22745, d128411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22745, d128411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128412 q = 1) (hb : d194495 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128412, d194495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128412, d194495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro49103 (p : Pattern) (ha : d128422 p = 1) (hb : d194514 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d17429 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d194509 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d128418 q = 1) (hb : d194510 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128418, d194510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d128418, d194510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d17485 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128419 q = 1) (hb : d194511 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128419, d194511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128419, d194511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d128420 q = 1) (hb : d194512 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128420, d194512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128420, d194512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128421 q = 1) (hb : d194513 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128421, d194513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128421, d194513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128422 q = 1) (hb : d194514 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128422, d194514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128422, d194514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49104 (p : Pattern) (ha : d128428 p = 1) (hb : d194520 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d17207 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22747 q = 1) (hb : d128406 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d22747, d128406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49100 q ha hb
    | true =>
      simp only [d22747, d128406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49101 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d17355 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d22748 q = 1) (hb : d128407 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d22748, d128407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22748, d128407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d128408 q = 1) (hb : d194493 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128408, d194493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d128408, d194493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128409 q = 1) (hb : d194494 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128409, d194494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d128409, d194494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128413 q = 1) (hb : d194496 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128413, d194496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128413, d194496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49102 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d17364 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d128414 q = 1) (hb : d194497 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128414, d194497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128414, d194497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d128415 q = 1) (hb : d194498 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128415, d194498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128415, d194498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d128416 q = 1) (hb : d194499 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128416, d194499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128416, d194499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d128417 q = 1) (hb : d194500 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128417, d194500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128417, d194500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128423 q = 1) (hb : d194515 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128423, d194515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128423, d194515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49103 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d17501 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d128424 q = 1) (hb : d194516 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128424, d194516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128424, d194516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d128425 q = 1) (hb : d194517 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128425, d194517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128425, d194517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d128426 q = 1) (hb : d194518 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128426, d194518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128426, d194518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d128427 q = 1) (hb : d194519 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128427, d194519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128427, d194519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d128428 q = 1) (hb : d194520 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128428, d194520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128428, d194520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro49105 (p : Pattern) (ha : d128434 p = 1) (hb : d194526 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128429 q = 1) (hb : d194521 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128429, d194521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128429, d194521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49104 q ha hb
  have h2 (q : Pattern) (ha : d128430 q = 1) (hb : d194522 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128430, d194522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128430, d194522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128431 q = 1) (hb : d194523 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128431, d194523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128431, d194523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128432 q = 1) (hb : d194524 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128432, d194524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128432, d194524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128433 q = 1) (hb : d194525 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128433, d194525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128433, d194525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128434 q = 1) (hb : d194526 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128434, d194526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128434, d194526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49106 (p : Pattern) (ha : d128440 p = 1) (hb : d194532 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d128269 q = 1) (hb : d194389 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128269, d194389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49075 q ha hb
    | true =>
      simp only [d128269, d194389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49081 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d128309 q = 1) (hb : d194416 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128309, d194416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128309, d194416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49087 q ha hb
  have h3 (q : Pattern) (ha : d128310 q = 1) (hb : d194417 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128310, d194417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128310, d194417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128350 q = 1) (hb : d194452 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128350, d194452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128350, d194452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49093 q ha hb
  have h5 (q : Pattern) (ha : d128351 q = 1) (hb : d194453 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128351, d194453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128351, d194453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128352 q = 1) (hb : d194454 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128352, d194454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128352, d194454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128392 q = 1) (hb : d194489 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128392, d194489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128392, d194489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49099 q ha hb
  have h8 (q : Pattern) (ha : d128393 q = 1) (hb : d194490 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128393, d194490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128393, d194490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128394 q = 1) (hb : d194491 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128394, d194491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128394, d194491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128395 q = 1) (hb : d194492 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d128395, d194492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128395, d194492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128435 q = 1) (hb : d194527 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d128435, d194527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128435, d194527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49105 q ha hb
  have h12 (q : Pattern) (ha : d128436 q = 1) (hb : d194528 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d128436, d194528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128436, d194528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128437 q = 1) (hb : d194529 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d128437, d194529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128437, d194529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128438 q = 1) (hb : d194530 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d128438, d194530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128438, d194530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128439 q = 1) (hb : d194531 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d128439, d194531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128439, d194531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128440 q = 1) (hb : d194532 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d128440, d194532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128440, d194532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro49107 (p : Pattern) (ha : d128446 p = 1) (hb : d194538 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128441 q = 1) (hb : d194533 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d128441, d194533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49106 q ha hb
    | true =>
      simp only [d128441, d194533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128442 q = 1) (hb : d194534 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d128442, d194534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128442, d194534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128443 q = 1) (hb : d194535 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d128443, d194535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128443, d194535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128444 q = 1) (hb : d194536 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d128444, d194536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128444, d194536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128445 q = 1) (hb : d194537 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d128445, d194537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128445, d194537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128446 q = 1) (hb : d194538 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d128446, d194538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128446, d194538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49108 (p : Pattern) (ha : d128452 p = 1) (hb : d194544 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128447 q = 1) (hb : d194539 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d128447, d194539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49107 q ha hb
    | true =>
      simp only [d128447, d194539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128448 q = 1) (hb : d194540 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d128448, d194540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128448, d194540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128449 q = 1) (hb : d194541 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d128449, d194541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128449, d194541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128450 q = 1) (hb : d194542 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d128450, d194542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128450, d194542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128451 q = 1) (hb : d194543 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d128451, d194543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128451, d194543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128452 q = 1) (hb : d194544 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d128452, d194544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128452, d194544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49109 (p : Pattern) (ha : d128458 p = 1) (hb : d194550 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128453 q = 1) (hb : d194545 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d128453, d194545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49108 q ha hb
    | true =>
      simp only [d128453, d194545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128454 q = 1) (hb : d194546 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d128454, d194546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128454, d194546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128455 q = 1) (hb : d194547 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d128455, d194547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128455, d194547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128456 q = 1) (hb : d194548 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d128456, d194548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128456, d194548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128457 q = 1) (hb : d194549 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d128457, d194549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128457, d194549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128458 q = 1) (hb : d194550 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d128458, d194550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128458, d194550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49110 (p : Pattern) (ha : d128464 p = 1) (hb : d194556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128459 q = 1) (hb : d194551 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d128459, d194551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49109 q ha hb
    | true =>
      simp only [d128459, d194551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128460 q = 1) (hb : d194552 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d128460, d194552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128460, d194552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128461 q = 1) (hb : d194553 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d128461, d194553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128461, d194553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128462 q = 1) (hb : d194554 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d128462, d194554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128462, d194554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128463 q = 1) (hb : d194555 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d128463, d194555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128463, d194555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128464 q = 1) (hb : d194556 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d128464, d194556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128464, d194556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49111 (p : Pattern) (ha : d128470 p = 1) (hb : d194562 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128465 q = 1) (hb : d194557 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d128465, d194557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49110 q ha hb
    | true =>
      simp only [d128465, d194557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128466 q = 1) (hb : d194558 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d128466, d194558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128466, d194558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128467 q = 1) (hb : d194559 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d128467, d194559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128467, d194559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128468 q = 1) (hb : d194560 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d128468, d194560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128468, d194560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128469 q = 1) (hb : d194561 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d128469, d194561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128469, d194561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128470 q = 1) (hb : d194562 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d128470, d194562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128470, d194562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49112 (p : Pattern) (ha : d128476 p = 1) (hb : d194568 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128471 q = 1) (hb : d194563 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d128471, d194563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49111 q ha hb
    | true =>
      simp only [d128471, d194563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128472 q = 1) (hb : d194564 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d128472, d194564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128472, d194564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128473 q = 1) (hb : d194565 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d128473, d194565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128473, d194565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128474 q = 1) (hb : d194566 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d128474, d194566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128474, d194566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128475 q = 1) (hb : d194567 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d128475, d194567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128475, d194567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128476 q = 1) (hb : d194568 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d128476, d194568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128476, d194568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49113 (p : Pattern) (ha : d128482 p = 1) (hb : d194574 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128477 q = 1) (hb : d194569 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d128477, d194569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49112 q ha hb
    | true =>
      simp only [d128477, d194569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d128478 q = 1) (hb : d194570 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d128478, d194570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128478, d194570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d128479 q = 1) (hb : d194571 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d128479, d194571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128479, d194571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d128480 q = 1) (hb : d194572 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d128480, d194572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d128480, d194572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128481 q = 1) (hb : d194573 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d128481, d194573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128481, d194573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d128482 q = 1) (hb : d194574 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d128482, d194574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128482, d194574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49114 (p : Pattern) (ha : d150302 p = 1) (hb : d207966 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d150301 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d207965 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d150302 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d150302, d207966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d150302, d207966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro49115 (p : Pattern) (ha : d150308 p = 1) (hb : d207966 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150303 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d150303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49114 q ha hb
    | true =>
      simp only [d150303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150304 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d150304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150305 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d150305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150306 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d150306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150307 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d150307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150308 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d150308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49116 (p : Pattern) (ha : d150314 p = 1) (hb : d207966 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150309 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d150309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49115 q ha hb
    | true =>
      simp only [d150309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150310 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d150310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150311 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d150311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150312 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d150312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150313 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d150313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150314 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d150314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49117 (p : Pattern) (ha : d150320 p = 1) (hb : d207966 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150315 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d150315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49116 q ha hb
    | true =>
      simp only [d150315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150316 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d150316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150317 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d150317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150318 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d150318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150319 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d150319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150320 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d150320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49118 (p : Pattern) (ha : d150326 p = 1) (hb : d207966 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150321 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d150321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49117 q ha hb
    | true =>
      simp only [d150321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150322 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d150322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150323 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d150323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150324 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d150324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150325 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d150325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150326 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d150326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49119 (p : Pattern) (ha : d194550 p = 1) (hb : d207966 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d194549 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d207965 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d194550 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d194550, d207966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d194550, d207966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h2 p ha hb
theorem andIntro49120 (p : Pattern) (ha : d194556 p = 1) (hb : d207966 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194551 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d194551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49119 q ha hb
    | true =>
      simp only [d194551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d194552 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d194552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194553 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d194553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194554 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d194554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d194555 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d194555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d194556 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d194556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49121 (p : Pattern) (ha : d194562 p = 1) (hb : d207966 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194557 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d194557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49120 q ha hb
    | true =>
      simp only [d194557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d194558 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d194558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194559 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d194559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194560 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d194560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d194561 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d194561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d194562 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d194562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49122 (p : Pattern) (ha : d194568 p = 1) (hb : d207966 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194563 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d194563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49121 q ha hb
    | true =>
      simp only [d194563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d194564 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d194564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194565 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d194565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194566 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d194566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d194567 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d194567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d194568 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d194568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49123 (p : Pattern) (ha : d194574 p = 1) (hb : d207966 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d194569 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d194569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49122 q ha hb
    | true =>
      simp only [d194569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d194570 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d194570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d194570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d194571 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d194571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d194571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d194572 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d194572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d194572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d194573 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d194573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d194573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d194574 q = 1) (hb : d207966 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d194574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d194574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49124 (p : Pattern) (ha : d20893 p = 1) (hb : d169395 p = 1) : d169398 p = 1 := by
  have h0 (q : Pattern) (ha : d754 q = 1) (hb : d116750 q = 1) : d754 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d28 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20892 q = 1) (hb : d169395 q = 1) : d757 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d20892, d169395, d757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20892, d169395, d757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d29 q = 1) (hb : d169395 q = 1) : d29 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20893 q = 1) (hb : d169395 q = 1) : d169398 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d20893, d169398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20893, d169398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro49125 (p : Pattern) (ha : d20899 p = 1) (hb : d169395 p = 1) : d169404 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d169395 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20894 q = 1) (hb : d169395 q = 1) : d169399 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20894, d169399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49124 q ha hb
    | true =>
      simp only [d20894, d169399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20895 q = 1) (hb : d169395 q = 1) : d169400 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20895, d169400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20895, d169400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20896 q = 1) (hb : d169395 q = 1) : d169401 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20896, d169401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20896, d169401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d169395 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d20897 q = 1) (hb : d169395 q = 1) : d169402 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20897, d169402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20897, d169402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d169395 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d20898 q = 1) (hb : d169395 q = 1) : d169403 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20898, d169403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20898, d169403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20899 q = 1) (hb : d169395 q = 1) : d169404 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20899, d169404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20899, d169404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro49126 (p : Pattern) (ha : d20905 p = 1) (hb : d169395 p = 1) : d169410 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d169395 q = 1) : d169405 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49125 q ha hb
    | true =>
      simp only [d20900, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d169395 q = 1) : d169406 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d169395 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20902 q = 1) (hb : d169395 q = 1) : d169407 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d169407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d169407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20903 q = 1) (hb : d169395 q = 1) : d169408 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20903, d169408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20903, d169408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20904 q = 1) (hb : d169395 q = 1) : d169409 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20904, d169409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20904, d169409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20905 q = 1) (hb : d169395 q = 1) : d169410 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20905, d169410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20905, d169410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro49127 (p : Pattern) (ha : d150001 p = 1) (hb : d169395 p = 1) : d169416 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d169395 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d169395 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d169395 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20906 q = 1) (hb : d169395 q = 1) : d169411 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d169411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49126 q ha hb
    | true =>
      simp only [d20906, d169411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d149997 q = 1) (hb : d169395 q = 1) : d169412 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d149997, d169412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d149997, d169412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d169395 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d149998 q = 1) (hb : d169395 q = 1) : d169413 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d149998, d169413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d149998, d169413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d149999 q = 1) (hb : d169395 q = 1) : d169414 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d149999, d169414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d149999, d169414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150000 q = 1) (hb : d169395 q = 1) : d169415 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150000, d169415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150000, d169415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150001 q = 1) (hb : d169395 q = 1) : d169416 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150001, d169416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150001, d169416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro49128 (p : Pattern) (ha : d20912 p = 1) (hb : d169395 p = 1) : d169417 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d169395 q = 1) : d169405 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49125 q ha hb
    | true =>
      simp only [d20900, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d169395 q = 1) : d169406 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d169395 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20902 q = 1) (hb : d169395 q = 1) : d169407 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d169407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d169407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20903 q = 1) (hb : d169395 q = 1) : d169408 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20903, d169408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20903, d169408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20904 q = 1) (hb : d169395 q = 1) : d169409 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20904, d169409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20904, d169409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20912 q = 1) (hb : d169395 q = 1) : d169417 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20912, d169417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20912, d169417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro49129 (p : Pattern) (ha : d150006 p = 1) (hb : d169395 p = 1) : d169423 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d169395 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d169395 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d169395 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d20906 q = 1) (hb : d169395 q = 1) : d169411 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d169411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49126 q ha hb
    | true =>
      simp only [d20906, d169411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d149997 q = 1) (hb : d169395 q = 1) : d169412 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d149997, d169412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d149997, d169412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d169395 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d149998 q = 1) (hb : d169395 q = 1) : d169413 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d149998, d169413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d149998, d169413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d149999 q = 1) (hb : d169395 q = 1) : d169414 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d149999, d169414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d149999, d169414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150000 q = 1) (hb : d169395 q = 1) : d169415 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150000, d169415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150000, d169415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d169395 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d169395 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d169395 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d20913 q = 1) (hb : d169395 q = 1) : d169418 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20913, d169418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49128 q ha hb
    | true =>
      simp only [d20913, d169418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150002 q = 1) (hb : d169395 q = 1) : d169419 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150002, d169419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150002, d169419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d169395 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d150003 q = 1) (hb : d169395 q = 1) : d169420 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150003, d169420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150003, d169420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d150004 q = 1) (hb : d169395 q = 1) : d169421 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150004, d169421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150004, d169421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d150005 q = 1) (hb : d169395 q = 1) : d169422 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150005, d169422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150005, d169422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d150006 q = 1) (hb : d169395 q = 1) : d169423 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150006, d169423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150006, d169423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro49130 (p : Pattern) (ha : d150013 p = 1) (hb : d169395 p = 1) : d169430 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d169395 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20913 q = 1) (hb : d169395 q = 1) : d169418 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20913, d169418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49128 q ha hb
    | true =>
      simp only [d20913, d169418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150002 q = 1) (hb : d169395 q = 1) : d169419 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150002, d169419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150002, d169419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d169395 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150003 q = 1) (hb : d169395 q = 1) : d169420 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150003, d169420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150003, d169420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150011 q = 1) (hb : d169395 q = 1) : d169428 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150011, d169428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150011, d169428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150012 q = 1) (hb : d169395 q = 1) : d169429 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150012, d169429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150012, d169429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150013 q = 1) (hb : d169395 q = 1) : d169430 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150013, d169430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150013, d169430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49131 (p : Pattern) (ha : d20932 p = 1) (hb : d169395 p = 1) : d169436 p = 1 := by
  have h0 (q : Pattern) (ha : d974 q = 1) (hb : d116750 q = 1) : d974 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20931 q = 1) (hb : d169395 q = 1) : d980 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d20931, d169395, d980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20931, d169395, d980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d70 q = 1) (hb : d169395 q = 1) : d70 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20932 q = 1) (hb : d169395 q = 1) : d169436 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d20932, d169436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20932, d169436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro49132 (p : Pattern) (ha : d20938 p = 1) (hb : d169395 p = 1) : d169442 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d169395 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20933 q = 1) (hb : d169395 q = 1) : d169437 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20933, d169437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49131 q ha hb
    | true =>
      simp only [d20933, d169437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20934 q = 1) (hb : d169395 q = 1) : d169438 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20934, d169438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20934, d169438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20935 q = 1) (hb : d169395 q = 1) : d169439 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20935, d169439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20935, d169439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d169395 q = 1) : d74 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d20936 q = 1) (hb : d169395 q = 1) : d169440 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20936, d169440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20936, d169440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d169395 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d20937 q = 1) (hb : d169395 q = 1) : d169441 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d20937, d169441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20937, d169441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20938 q = 1) (hb : d169395 q = 1) : d169442 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d20938, d169442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20938, d169442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro49133 (p : Pattern) (ha : d20944 p = 1) (hb : d169395 p = 1) : d169448 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20939 q = 1) (hb : d169395 q = 1) : d169443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20939, d169443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49132 q ha hb
    | true =>
      simp only [d20939, d169443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20940 q = 1) (hb : d169395 q = 1) : d169444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20940, d169444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20940, d169444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d169395 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20941 q = 1) (hb : d169395 q = 1) : d169445 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20941, d169445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20941, d169445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20942 q = 1) (hb : d169395 q = 1) : d169446 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20942, d169446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20942, d169446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20943 q = 1) (hb : d169395 q = 1) : d169447 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20943, d169447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20943, d169447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20944 q = 1) (hb : d169395 q = 1) : d169448 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20944, d169448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20944, d169448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro49134 (p : Pattern) (ha : d150023 p = 1) (hb : d169395 p = 1) : d169454 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d169395 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20945 q = 1) (hb : d169395 q = 1) : d169449 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20945, d169449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49133 q ha hb
    | true =>
      simp only [d20945, d169449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150019 q = 1) (hb : d169395 q = 1) : d169450 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150019, d169450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150019, d169450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d169395 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150020 q = 1) (hb : d169395 q = 1) : d169451 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150020, d169451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150020, d169451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150021 q = 1) (hb : d169395 q = 1) : d169452 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150021, d169452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150021, d169452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150022 q = 1) (hb : d169395 q = 1) : d169453 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150022, d169453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150022, d169453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150023 q = 1) (hb : d169395 q = 1) : d169454 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150023, d169454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150023, d169454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49135 (p : Pattern) (ha : d150029 p = 1) (hb : d169395 p = 1) : d169460 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d169395 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150007 q = 1) (hb : d169395 q = 1) : d169424 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150007, d169424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49127 q ha hb
    | true =>
      simp only [d150007, d169424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49129 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d169395 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d150008 q = 1) (hb : d169395 q = 1) : d169425 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150008, d169425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150008, d169425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d150009 q = 1) (hb : d169395 q = 1) : d169426 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150009, d169426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150009, d169426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150010 q = 1) (hb : d169395 q = 1) : d169427 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150010, d169427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150010, d169427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150014 q = 1) (hb : d169395 q = 1) : d169431 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150014, d169431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150014, d169431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49130 q ha hb
  have h8 (q : Pattern) (ha : d150015 q = 1) (hb : d169395 q = 1) : d169432 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150015, d169432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150015, d169432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d150016 q = 1) (hb : d169395 q = 1) : d169433 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150016, d169433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150016, d169433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d150017 q = 1) (hb : d169395 q = 1) : d169434 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150017, d169434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150017, d169434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d150018 q = 1) (hb : d169395 q = 1) : d169435 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150018, d169435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150018, d169435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d150024 q = 1) (hb : d169395 q = 1) : d169455 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150024, d169455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150024, d169455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49134 q ha hb
  have h13 (q : Pattern) (ha : d150025 q = 1) (hb : d169395 q = 1) : d169456 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150025, d169456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150025, d169456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d150026 q = 1) (hb : d169395 q = 1) : d169457 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150026, d169457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150026, d169457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d150027 q = 1) (hb : d169395 q = 1) : d169458 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150027, d169458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150027, d169458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d150028 q = 1) (hb : d169395 q = 1) : d169459 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150028, d169459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150028, d169459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d150029 q = 1) (hb : d169395 q = 1) : d169460 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150029, d169460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150029, d169460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro49136 (p : Pattern) (ha : d20966 p = 1) (hb : d169395 p = 1) : d169470 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d169395 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20906 q = 1) (hb : d169395 q = 1) : d169411 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d169411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49126 q ha hb
    | true =>
      simp only [d20906, d169411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20962 q = 1) (hb : d169395 q = 1) : d169466 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20962, d169466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20962, d169466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20963 q = 1) (hb : d169395 q = 1) : d169467 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20963, d169467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20963, d169467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20964 q = 1) (hb : d169395 q = 1) : d169468 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20964, d169468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20964, d169468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20965 q = 1) (hb : d169395 q = 1) : d169469 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20965, d169469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20965, d169469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20966 q = 1) (hb : d169395 q = 1) : d169470 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20966, d169470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20966, d169470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro49137 (p : Pattern) (ha : d20973 p = 1) (hb : d169395 p = 1) : d169477 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d169395 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20906 q = 1) (hb : d169395 q = 1) : d169411 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d169411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49126 q ha hb
    | true =>
      simp only [d20906, d169411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20962 q = 1) (hb : d169395 q = 1) : d169466 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20962, d169466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20962, d169466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20963 q = 1) (hb : d169395 q = 1) : d169467 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20963, d169467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20963, d169467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20964 q = 1) (hb : d169395 q = 1) : d169468 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20964, d169468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20964, d169468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20965 q = 1) (hb : d169395 q = 1) : d169469 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20965, d169469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20965, d169469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d169395 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d20913 q = 1) (hb : d169395 q = 1) : d169418 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20913, d169418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49128 q ha hb
    | true =>
      simp only [d20913, d169418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20969 q = 1) (hb : d169395 q = 1) : d169473 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20969, d169473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20969, d169473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20970 q = 1) (hb : d169395 q = 1) : d169474 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20970, d169474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d20970, d169474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d20971 q = 1) (hb : d169395 q = 1) : d169475 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20971, d169475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20971, d169475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d20972 q = 1) (hb : d169395 q = 1) : d169476 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20972, d169476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20972, d169476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d20973 q = 1) (hb : d169395 q = 1) : d169477 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d20973, d169477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d20973, d169477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro49138 (p : Pattern) (ha : d21058 p = 1) (hb : d169395 p = 1) : d169539 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d169395 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20906 q = 1) (hb : d169395 q = 1) : d169411 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20906, d169411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49126 q ha hb
    | true =>
      simp only [d20906, d169411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20962 q = 1) (hb : d169395 q = 1) : d169466 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20962, d169466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20962, d169466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20963 q = 1) (hb : d169395 q = 1) : d169467 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20963, d169467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20963, d169467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20964 q = 1) (hb : d169395 q = 1) : d169468 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20964, d169468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20964, d169468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20965 q = 1) (hb : d169395 q = 1) : d169469 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d20965, d169469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20965, d169469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d169395 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d21058 q = 1) (hb : d169395 q = 1) : d169539 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21058, d169539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21058, d169539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49139 (p : Pattern) (ha : d20978 p = 1) (hb : d169395 p = 1) : d169482 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d169395 q = 1) : d169405 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49125 q ha hb
    | true =>
      simp only [d20900, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d169395 q = 1) : d169406 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d169395 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20902 q = 1) (hb : d169395 q = 1) : d169407 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d169407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d169407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20903 q = 1) (hb : d169395 q = 1) : d169408 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20903, d169408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20903, d169408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20977 q = 1) (hb : d169395 q = 1) : d169481 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20977, d169481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20977, d169481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20978 q = 1) (hb : d169395 q = 1) : d169482 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20978, d169482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20978, d169482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro49140 (p : Pattern) (ha : d20985 p = 1) (hb : d169395 p = 1) : d169489 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d169395 q = 1) : d169405 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49125 q ha hb
    | true =>
      simp only [d20900, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d169395 q = 1) : d169406 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d169395 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20902 q = 1) (hb : d169395 q = 1) : d169407 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d169407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d169407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20983 q = 1) (hb : d169395 q = 1) : d169487 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20983, d169487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20983, d169487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20984 q = 1) (hb : d169395 q = 1) : d169488 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20984, d169488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20984, d169488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d20985 q = 1) (hb : d169395 q = 1) : d169489 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d20985, d169489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20985, d169489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro49141 (p : Pattern) (ha : d20996 p = 1) (hb : d169395 p = 1) : d169494 p = 1 := by
  have h0 (q : Pattern) (ha : d20993 q = 1) (hb : d116750 q = 1) : d20993 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d754 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20994 q = 1) (hb : d169395 q = 1) : d169493 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d20994, d169395, d169493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20994, d169395, d169493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d5454 q = 1) (hb : d116750 q = 1) : d5454 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d28 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d20995 q = 1) (hb : d169395 q = 1) : d5455 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d20995, d169395, d5455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20995, d169395, d5455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d20996 q = 1) (hb : d169395 q = 1) : d169494 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d20996, d169494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20996, d169494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49142 (p : Pattern) (ha : d21002 p = 1) (hb : d169395 p = 1) : d169500 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20997 q = 1) (hb : d169395 q = 1) : d169495 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20997, d169495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49141 q ha hb
    | true =>
      simp only [d20997, d169495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49124 q ha hb
  have h2 (q : Pattern) (ha : d20998 q = 1) (hb : d169395 q = 1) : d169496 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20998, d169496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20998, d169496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20999 q = 1) (hb : d169395 q = 1) : d169497 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20999, d169497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20999, d169497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d169395 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d20894 q = 1) (hb : d169395 q = 1) : d169399 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20894, d169399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49124 q ha hb
    | true =>
      simp only [d20894, d169399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20895 q = 1) (hb : d169395 q = 1) : d169400 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20895, d169400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20895, d169400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20896 q = 1) (hb : d169395 q = 1) : d169401 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20896, d169401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20896, d169401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21000 q = 1) (hb : d169395 q = 1) : d169498 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21000, d169498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21000, d169498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33 q = 1) (hb : d169395 q = 1) : d33 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d20897 q = 1) (hb : d169395 q = 1) : d169402 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20897, d169402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20897, d169402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21001 q = 1) (hb : d169395 q = 1) : d169499 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21001, d169499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21001, d169499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d21002 q = 1) (hb : d169395 q = 1) : d169500 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21002, d169500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21002, d169500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro49143 (p : Pattern) (ha : d21008 p = 1) (hb : d169395 p = 1) : d169506 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21003 q = 1) (hb : d169395 q = 1) : d169501 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21003, d169501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49142 q ha hb
    | true =>
      simp only [d21003, d169501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21004 q = 1) (hb : d169395 q = 1) : d169502 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21004, d169502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21004, d169502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20900 q = 1) (hb : d169395 q = 1) : d169405 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49125 q ha hb
    | true =>
      simp only [d20900, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20901 q = 1) (hb : d169395 q = 1) : d169406 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21005 q = 1) (hb : d169395 q = 1) : d169503 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21005, d169503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21005, d169503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21006 q = 1) (hb : d169395 q = 1) : d169504 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21006, d169504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21006, d169504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21007 q = 1) (hb : d169395 q = 1) : d169505 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21007, d169505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21007, d169505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21008 q = 1) (hb : d169395 q = 1) : d169506 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21008, d169506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21008, d169506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49144 (p : Pattern) (ha : d21029 p = 1) (hb : d169395 p = 1) : d169512 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d169395 q = 1) : d169405 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49125 q ha hb
    | true =>
      simp only [d20900, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d169395 q = 1) : d169406 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21026 q = 1) (hb : d169395 q = 1) : d169509 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21026, d169509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21026, d169509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21027 q = 1) (hb : d169395 q = 1) : d169510 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21027, d169510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21027, d169510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21028 q = 1) (hb : d169395 q = 1) : d169511 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21028, d169511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21028, d169511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21029 q = 1) (hb : d169395 q = 1) : d169512 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21029, d169512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21029, d169512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49145 (p : Pattern) (ha : d150039 p = 1) (hb : d169395 p = 1) : d169518 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d169395 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20979 q = 1) (hb : d169395 q = 1) : d169483 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20979, d169483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49139 q ha hb
    | true =>
      simp only [d20979, d169483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20980 q = 1) (hb : d169395 q = 1) : d169484 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20980, d169484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20980, d169484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20981 q = 1) (hb : d169395 q = 1) : d169485 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20981, d169485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20981, d169485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20982 q = 1) (hb : d169395 q = 1) : d169486 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20982, d169486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20982, d169486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d169395 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d20986 q = 1) (hb : d169395 q = 1) : d169490 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20986, d169490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49140 q ha hb
    | true =>
      simp only [d20986, d169490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20987 q = 1) (hb : d169395 q = 1) : d169491 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20987, d169491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20987, d169491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20988 q = 1) (hb : d169395 q = 1) : d169492 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20988, d169492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20988, d169492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21009 q = 1) (hb : d169395 q = 1) : d169507 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21009, d169507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49143 q ha hb
    | true =>
      simp only [d21009, d169507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49126 q ha hb
  have h11 (q : Pattern) (ha : d150035 q = 1) (hb : d169395 q = 1) : d169508 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150035, d169508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150035, d169508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d21030 q = 1) (hb : d169395 q = 1) : d169513 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21030, d169513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49144 q ha hb
    | true =>
      simp only [d21030, d169513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d21031 q = 1) (hb : d169395 q = 1) : d169514 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21031, d169514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21031, d169514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d150036 q = 1) (hb : d169395 q = 1) : d169515 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150036, d169515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150036, d169515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d150037 q = 1) (hb : d169395 q = 1) : d169516 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150037, d169516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150037, d169516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d150038 q = 1) (hb : d169395 q = 1) : d169517 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150038, d169517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150038, d169517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d150039 q = 1) (hb : d169395 q = 1) : d169518 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150039, d169518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150039, d169518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro49146 (p : Pattern) (ha : d21036 p = 1) (hb : d169395 p = 1) : d169519 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d169395 q = 1) : d169405 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49125 q ha hb
    | true =>
      simp only [d20900, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d169395 q = 1) : d169406 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d169395 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20902 q = 1) (hb : d169395 q = 1) : d169407 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d169407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d169407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20903 q = 1) (hb : d169395 q = 1) : d169408 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20903, d169408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d20903, d169408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d20977 q = 1) (hb : d169395 q = 1) : d169481 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20977, d169481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20977, d169481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21036 q = 1) (hb : d169395 q = 1) : d169519 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21036, d169519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21036, d169519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro49147 (p : Pattern) (ha : d21041 p = 1) (hb : d169395 p = 1) : d169524 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d169395 q = 1) : d169405 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49125 q ha hb
    | true =>
      simp only [d20900, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d169395 q = 1) : d169406 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d169395 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d20902 q = 1) (hb : d169395 q = 1) : d169407 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d20902, d169407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20902, d169407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d20983 q = 1) (hb : d169395 q = 1) : d169487 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d20983, d169487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20983, d169487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20984 q = 1) (hb : d169395 q = 1) : d169488 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d20984, d169488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d20984, d169488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21041 q = 1) (hb : d169395 q = 1) : d169524 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21041, d169524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21041, d169524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro49148 (p : Pattern) (ha : d21045 p = 1) (hb : d169395 p = 1) : d169528 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21003 q = 1) (hb : d169395 q = 1) : d169501 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21003, d169501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49142 q ha hb
    | true =>
      simp only [d21003, d169501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21004 q = 1) (hb : d169395 q = 1) : d169502 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21004, d169502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21004, d169502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20900 q = 1) (hb : d169395 q = 1) : d169405 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49125 q ha hb
    | true =>
      simp only [d20900, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20901 q = 1) (hb : d169395 q = 1) : d169406 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21005 q = 1) (hb : d169395 q = 1) : d169503 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21005, d169503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21005, d169503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21006 q = 1) (hb : d169395 q = 1) : d169504 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21006, d169504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21006, d169504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21007 q = 1) (hb : d169395 q = 1) : d169505 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21007, d169505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21007, d169505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21045 q = 1) (hb : d169395 q = 1) : d169528 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21045, d169528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21045, d169528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49149 (p : Pattern) (ha : d21050 p = 1) (hb : d169395 p = 1) : d169531 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20900 q = 1) (hb : d169395 q = 1) : d169405 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20900, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49125 q ha hb
    | true =>
      simp only [d20900, d169405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20901 q = 1) (hb : d169395 q = 1) : d169406 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20901, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20901, d169406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21026 q = 1) (hb : d169395 q = 1) : d169509 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21026, d169509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21026, d169509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21027 q = 1) (hb : d169395 q = 1) : d169510 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21027, d169510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21027, d169510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21028 q = 1) (hb : d169395 q = 1) : d169511 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21028, d169511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21028, d169511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21050 q = 1) (hb : d169395 q = 1) : d169531 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21050, d169531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21050, d169531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49150 (p : Pattern) (ha : d150044 p = 1) (hb : d169395 p = 1) : d169537 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d169395 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20979 q = 1) (hb : d169395 q = 1) : d169483 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20979, d169483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49139 q ha hb
    | true =>
      simp only [d20979, d169483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20980 q = 1) (hb : d169395 q = 1) : d169484 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20980, d169484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20980, d169484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20981 q = 1) (hb : d169395 q = 1) : d169485 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20981, d169485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20981, d169485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20982 q = 1) (hb : d169395 q = 1) : d169486 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d20982, d169486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20982, d169486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d169395 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d20986 q = 1) (hb : d169395 q = 1) : d169490 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d20986, d169490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49140 q ha hb
    | true =>
      simp only [d20986, d169490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20987 q = 1) (hb : d169395 q = 1) : d169491 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d20987, d169491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20987, d169491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d20988 q = 1) (hb : d169395 q = 1) : d169492 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d20988, d169492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d20988, d169492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21009 q = 1) (hb : d169395 q = 1) : d169507 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21009, d169507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49143 q ha hb
    | true =>
      simp only [d21009, d169507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49126 q ha hb
  have h11 (q : Pattern) (ha : d150035 q = 1) (hb : d169395 q = 1) : d169508 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150035, d169508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150035, d169508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d21030 q = 1) (hb : d169395 q = 1) : d169513 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21030, d169513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49144 q ha hb
    | true =>
      simp only [d21030, d169513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d21031 q = 1) (hb : d169395 q = 1) : d169514 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21031, d169514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21031, d169514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d150036 q = 1) (hb : d169395 q = 1) : d169515 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150036, d169515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150036, d169515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d150037 q = 1) (hb : d169395 q = 1) : d169516 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150037, d169516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150037, d169516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d150038 q = 1) (hb : d169395 q = 1) : d169517 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150038, d169517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150038, d169517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d169395 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d21037 q = 1) (hb : d169395 q = 1) : d169520 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21037, d169520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49146 q ha hb
    | true =>
      simp only [d21037, d169520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21038 q = 1) (hb : d169395 q = 1) : d169521 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21038, d169521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21038, d169521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d21039 q = 1) (hb : d169395 q = 1) : d169522 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21039, d169522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d21039, d169522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d21040 q = 1) (hb : d169395 q = 1) : d169523 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21040, d169523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21040, d169523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d169395 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d21042 q = 1) (hb : d169395 q = 1) : d169525 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21042, d169525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49147 q ha hb
    | true =>
      simp only [d21042, d169525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d21043 q = 1) (hb : d169395 q = 1) : d169526 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21043, d169526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21043, d169526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d21044 q = 1) (hb : d169395 q = 1) : d169527 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21044, d169527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d21044, d169527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d21046 q = 1) (hb : d169395 q = 1) : d169529 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21046, d169529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49148 q ha hb
    | true =>
      simp only [d21046, d169529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49128 q ha hb
  have h27 (q : Pattern) (ha : d150040 q = 1) (hb : d169395 q = 1) : d169530 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150040, d169530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d150040, d169530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d21051 q = 1) (hb : d169395 q = 1) : d169532 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21051, d169532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49149 q ha hb
    | true =>
      simp only [d21051, d169532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d21052 q = 1) (hb : d169395 q = 1) : d169533 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21052, d169533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d21052, d169533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d150041 q = 1) (hb : d169395 q = 1) : d169534 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150041, d169534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d150041, d169534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d150042 q = 1) (hb : d169395 q = 1) : d169535 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150042, d169535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d150042, d169535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d150043 q = 1) (hb : d169395 q = 1) : d169536 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150043, d169536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150043, d169536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d150044 q = 1) (hb : d169395 q = 1) : d169537 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150044, d169537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150044, d169537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro49151 (p : Pattern) (ha : d150051 p = 1) (hb : d169395 p = 1) : d169546 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21046 q = 1) (hb : d169395 q = 1) : d169529 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21046, d169529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49148 q ha hb
    | true =>
      simp only [d21046, d169529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49128 q ha hb
  have h2 (q : Pattern) (ha : d150040 q = 1) (hb : d169395 q = 1) : d169530 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150040, d169530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150040, d169530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21051 q = 1) (hb : d169395 q = 1) : d169532 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21051, d169532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49149 q ha hb
    | true =>
      simp only [d21051, d169532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21052 q = 1) (hb : d169395 q = 1) : d169533 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21052, d169533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21052, d169533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150041 q = 1) (hb : d169395 q = 1) : d169534 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150041, d169534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150041, d169534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150049 q = 1) (hb : d169395 q = 1) : d169544 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150049, d169544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150049, d169544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150050 q = 1) (hb : d169395 q = 1) : d169545 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150050, d169545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150050, d169545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150051 q = 1) (hb : d169395 q = 1) : d169546 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150051, d169546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150051, d169546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49152 (p : Pattern) (ha : d21077 p = 1) (hb : d169395 p = 1) : d169553 p = 1 := by
  have h0 (q : Pattern) (ha : d21074 q = 1) (hb : d116750 q = 1) : d21074 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d974 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21075 q = 1) (hb : d169395 q = 1) : d169552 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21075, d169395, d169552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21075, d169395, d169552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d5498 q = 1) (hb : d116750 q = 1) : d5498 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d69 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21076 q = 1) (hb : d169395 q = 1) : d5499 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21076, d169395, d5499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21076, d169395, d5499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d21077 q = 1) (hb : d169395 q = 1) : d169553 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21077, d169553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21077, d169553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49153 (p : Pattern) (ha : d21083 p = 1) (hb : d169395 p = 1) : d169559 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21078 q = 1) (hb : d169395 q = 1) : d169554 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21078, d169554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49152 q ha hb
    | true =>
      simp only [d21078, d169554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49131 q ha hb
  have h2 (q : Pattern) (ha : d21079 q = 1) (hb : d169395 q = 1) : d169555 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21079, d169555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21079, d169555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21080 q = 1) (hb : d169395 q = 1) : d169556 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21080, d169556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21080, d169556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d169395 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d20933 q = 1) (hb : d169395 q = 1) : d169437 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20933, d169437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49131 q ha hb
    | true =>
      simp only [d20933, d169437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20934 q = 1) (hb : d169395 q = 1) : d169438 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20934, d169438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20934, d169438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20935 q = 1) (hb : d169395 q = 1) : d169439 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20935, d169439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20935, d169439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21081 q = 1) (hb : d169395 q = 1) : d169557 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21081, d169557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21081, d169557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74 q = 1) (hb : d169395 q = 1) : d74 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d20936 q = 1) (hb : d169395 q = 1) : d169440 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d20936, d169440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20936, d169440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21082 q = 1) (hb : d169395 q = 1) : d169558 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21082, d169558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21082, d169558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d21083 q = 1) (hb : d169395 q = 1) : d169559 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21083, d169559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d21083, d169559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro49154 (p : Pattern) (ha : d21089 p = 1) (hb : d169395 p = 1) : d169565 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21084 q = 1) (hb : d169395 q = 1) : d169560 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21084, d169560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49153 q ha hb
    | true =>
      simp only [d21084, d169560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21085 q = 1) (hb : d169395 q = 1) : d169561 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21085, d169561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21085, d169561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20939 q = 1) (hb : d169395 q = 1) : d169443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20939, d169443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49132 q ha hb
    | true =>
      simp only [d20939, d169443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d20940 q = 1) (hb : d169395 q = 1) : d169444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20940, d169444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20940, d169444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21086 q = 1) (hb : d169395 q = 1) : d169562 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21086, d169562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21086, d169562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21087 q = 1) (hb : d169395 q = 1) : d169563 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21087, d169563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21087, d169563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21088 q = 1) (hb : d169395 q = 1) : d169564 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21088, d169564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21088, d169564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21089 q = 1) (hb : d169395 q = 1) : d169565 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21089, d169565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21089, d169565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49155 (p : Pattern) (ha : d21110 p = 1) (hb : d169395 p = 1) : d169571 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20939 q = 1) (hb : d169395 q = 1) : d169443 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d20939, d169443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49132 q ha hb
    | true =>
      simp only [d20939, d169443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d20940 q = 1) (hb : d169395 q = 1) : d169444 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d20940, d169444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20940, d169444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21107 q = 1) (hb : d169395 q = 1) : d169568 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21107, d169568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21107, d169568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21108 q = 1) (hb : d169395 q = 1) : d169569 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21108, d169569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21108, d169569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21109 q = 1) (hb : d169395 q = 1) : d169570 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21109, d169570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21109, d169570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21110 q = 1) (hb : d169395 q = 1) : d169571 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21110, d169571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21110, d169571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49156 (p : Pattern) (ha : d150061 p = 1) (hb : d169395 p = 1) : d169577 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21090 q = 1) (hb : d169395 q = 1) : d169566 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21090, d169566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49154 q ha hb
    | true =>
      simp only [d21090, d169566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49133 q ha hb
  have h2 (q : Pattern) (ha : d150057 q = 1) (hb : d169395 q = 1) : d169567 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150057, d169567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150057, d169567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21111 q = 1) (hb : d169395 q = 1) : d169572 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21111, d169572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49155 q ha hb
    | true =>
      simp only [d21111, d169572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21112 q = 1) (hb : d169395 q = 1) : d169573 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21112, d169573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21112, d169573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150058 q = 1) (hb : d169395 q = 1) : d169574 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150058, d169574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150058, d169574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150059 q = 1) (hb : d169395 q = 1) : d169575 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150059, d169575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150059, d169575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150060 q = 1) (hb : d169395 q = 1) : d169576 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150060, d169576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150060, d169576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150061 q = 1) (hb : d169395 q = 1) : d169577 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150061, d169577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150061, d169577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49157 (p : Pattern) (ha : d150067 p = 1) (hb : d169395 p = 1) : d169583 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20967 q = 1) (hb : d169395 q = 1) : d169471 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20967, d169471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20967, d169471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49136 q ha hb
  have h2 (q : Pattern) (ha : d20968 q = 1) (hb : d169395 q = 1) : d169472 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20968, d169472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d20968, d169472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d20974 q = 1) (hb : d169395 q = 1) : d169478 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d20974, d169478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49136 q ha hb
    | true =>
      simp only [d20974, d169478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49137 q ha hb
  have h4 (q : Pattern) (ha : d20975 q = 1) (hb : d169395 q = 1) : d169479 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d20975, d169479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d20975, d169479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d20976 q = 1) (hb : d169395 q = 1) : d169480 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d20976, d169480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d20976, d169480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150045 q = 1) (hb : d169395 q = 1) : d169538 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150045, d169538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49145 q ha hb
    | true =>
      simp only [d150045, d169538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49150 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d169395 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d21059 q = 1) (hb : d169395 q = 1) : d169540 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21059, d169540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49138 q ha hb
    | true =>
      simp only [d21059, d169540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150046 q = 1) (hb : d169395 q = 1) : d169541 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150046, d169541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150046, d169541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150047 q = 1) (hb : d169395 q = 1) : d169542 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150047, d169542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150047, d169542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d150048 q = 1) (hb : d169395 q = 1) : d169543 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150048, d169543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150048, d169543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d150052 q = 1) (hb : d169395 q = 1) : d169547 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150052, d169547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150052, d169547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49151 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d169395 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d150053 q = 1) (hb : d169395 q = 1) : d169548 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150053, d169548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150053, d169548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d150054 q = 1) (hb : d169395 q = 1) : d169549 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150054, d169549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150054, d169549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d150055 q = 1) (hb : d169395 q = 1) : d169550 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150055, d169550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150055, d169550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d150056 q = 1) (hb : d169395 q = 1) : d169551 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150056, d169551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150056, d169551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d150062 q = 1) (hb : d169395 q = 1) : d169578 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150062, d169578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150062, d169578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49156 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d169395 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d150063 q = 1) (hb : d169395 q = 1) : d169579 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150063, d169579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d150063, d169579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d150064 q = 1) (hb : d169395 q = 1) : d169580 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150064, d169580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d150064, d169580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d150065 q = 1) (hb : d169395 q = 1) : d169581 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150065, d169581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150065, d169581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d150066 q = 1) (hb : d169395 q = 1) : d169582 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150066, d169582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d150066, d169582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d150067 q = 1) (hb : d169395 q = 1) : d169583 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150067, d169583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150067, d169583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro49158 (p : Pattern) (ha : d150073 p = 1) (hb : d169395 p = 1) : d169589 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d169395 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d150030 q = 1) (hb : d169395 q = 1) : d169461 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150030, d169461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150030, d169461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49135 q ha hb
  have h3 (q : Pattern) (ha : d150031 q = 1) (hb : d169395 q = 1) : d169462 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150031, d169462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150031, d169462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150032 q = 1) (hb : d169395 q = 1) : d169463 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150032, d169463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150032, d169463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150033 q = 1) (hb : d169395 q = 1) : d169464 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150033, d169464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150033, d169464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150034 q = 1) (hb : d169395 q = 1) : d169465 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150034, d169465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150034, d169465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150068 q = 1) (hb : d169395 q = 1) : d169584 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150068, d169584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150068, d169584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49157 q ha hb
  have h8 (q : Pattern) (ha : d150069 q = 1) (hb : d169395 q = 1) : d169585 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150069, d169585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150069, d169585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150070 q = 1) (hb : d169395 q = 1) : d169586 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150070, d169586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150070, d169586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150071 q = 1) (hb : d169395 q = 1) : d169587 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150071, d169587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150071, d169587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d150072 q = 1) (hb : d169395 q = 1) : d169588 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150072, d169588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150072, d169588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d150073 q = 1) (hb : d169395 q = 1) : d169589 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150073, d169589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150073, d169589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro49159 (p : Pattern) (ha : d21131 p = 1) (hb : d169395 p = 1) : d169592 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d20997 q = 1) (hb : d169395 q = 1) : d169495 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20997, d169495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49141 q ha hb
    | true =>
      simp only [d20997, d169495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49124 q ha hb
  have h2 (q : Pattern) (ha : d20998 q = 1) (hb : d169395 q = 1) : d169496 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20998, d169496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20998, d169496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20999 q = 1) (hb : d169395 q = 1) : d169497 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20999, d169497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20999, d169497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d169395 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d20894 q = 1) (hb : d169395 q = 1) : d169399 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20894, d169399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49124 q ha hb
    | true =>
      simp only [d20894, d169399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20895 q = 1) (hb : d169395 q = 1) : d169400 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20895, d169400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20895, d169400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20896 q = 1) (hb : d169395 q = 1) : d169401 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20896, d169401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20896, d169401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21000 q = 1) (hb : d169395 q = 1) : d169498 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21000, d169498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21000, d169498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21129 q = 1) (hb : d169395 q = 1) : d169590 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21129, d169590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21129, d169590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21130 q = 1) (hb : d169395 q = 1) : d169591 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21130, d169591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21130, d169591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21131 q = 1) (hb : d169395 q = 1) : d169592 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21131, d169592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21131, d169592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro49160 (p : Pattern) (ha : d21135 p = 1) (hb : d169395 p = 1) : d169596 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d169395 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20894 q = 1) (hb : d169395 q = 1) : d169399 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20894, d169399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49124 q ha hb
    | true =>
      simp only [d20894, d169399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20895 q = 1) (hb : d169395 q = 1) : d169400 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20895, d169400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20895, d169400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20896 q = 1) (hb : d169395 q = 1) : d169401 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20896, d169401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20896, d169401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21129 q = 1) (hb : d169395 q = 1) : d169590 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21129, d169590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21129, d169590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21134 q = 1) (hb : d169395 q = 1) : d169595 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21134, d169595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21134, d169595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21135 q = 1) (hb : d169395 q = 1) : d169596 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21135, d169596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21135, d169596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro49161 (p : Pattern) (ha : d21141 p = 1) (hb : d169395 p = 1) : d169602 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d169395 q = 1) : d169593 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49159 q ha hb
    | true =>
      simp only [d21132, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d169395 q = 1) : d169594 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21136 q = 1) (hb : d169395 q = 1) : d169597 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49160 q ha hb
    | true =>
      simp only [d21136, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21137 q = 1) (hb : d169395 q = 1) : d169598 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21138 q = 1) (hb : d169395 q = 1) : d169599 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21138, d169599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21138, d169599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21139 q = 1) (hb : d169395 q = 1) : d169600 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21139, d169600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21139, d169600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21140 q = 1) (hb : d169395 q = 1) : d169601 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21140, d169601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21140, d169601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21141 q = 1) (hb : d169395 q = 1) : d169602 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21141, d169602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21141, d169602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49162 (p : Pattern) (ha : d21145 p = 1) (hb : d169395 p = 1) : d169606 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21136 q = 1) (hb : d169395 q = 1) : d169597 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49160 q ha hb
    | true =>
      simp only [d21136, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21137 q = 1) (hb : d169395 q = 1) : d169598 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21142 q = 1) (hb : d169395 q = 1) : d169603 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21142, d169603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21142, d169603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21143 q = 1) (hb : d169395 q = 1) : d169604 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21143, d169604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21143, d169604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21144 q = 1) (hb : d169395 q = 1) : d169605 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21144, d169605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21144, d169605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21145 q = 1) (hb : d169395 q = 1) : d169606 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21145, d169606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21145, d169606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49163 (p : Pattern) (ha : d21151 p = 1) (hb : d169395 p = 1) : d169612 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21146 q = 1) (hb : d169395 q = 1) : d169607 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21146, d169607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49161 q ha hb
    | true =>
      simp only [d21146, d169607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49162 q ha hb
  have h2 (q : Pattern) (ha : d21147 q = 1) (hb : d169395 q = 1) : d169608 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21147, d169608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21147, d169608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21148 q = 1) (hb : d169395 q = 1) : d169609 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21148, d169609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21148, d169609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21149 q = 1) (hb : d169395 q = 1) : d169610 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21149, d169610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21149, d169610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21150 q = 1) (hb : d169395 q = 1) : d169611 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21150, d169611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21150, d169611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21151 q = 1) (hb : d169395 q = 1) : d169612 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21151, d169612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21151, d169612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49164 (p : Pattern) (ha : d21154 p = 1) (hb : d169395 p = 1) : d169615 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d169395 q = 1) : d169593 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49159 q ha hb
    | true =>
      simp only [d21132, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d169395 q = 1) : d169594 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21136 q = 1) (hb : d169395 q = 1) : d169597 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49160 q ha hb
    | true =>
      simp only [d21136, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21137 q = 1) (hb : d169395 q = 1) : d169598 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21138 q = 1) (hb : d169395 q = 1) : d169599 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21138, d169599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21138, d169599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21139 q = 1) (hb : d169395 q = 1) : d169600 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21139, d169600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21139, d169600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21140 q = 1) (hb : d169395 q = 1) : d169601 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21140, d169601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21140, d169601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21154 q = 1) (hb : d169395 q = 1) : d169615 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21154, d169615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21154, d169615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49165 (p : Pattern) (ha : d21155 p = 1) (hb : d169395 p = 1) : d169616 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21136 q = 1) (hb : d169395 q = 1) : d169597 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49160 q ha hb
    | true =>
      simp only [d21136, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21137 q = 1) (hb : d169395 q = 1) : d169598 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21142 q = 1) (hb : d169395 q = 1) : d169603 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21142, d169603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21142, d169603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21143 q = 1) (hb : d169395 q = 1) : d169604 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21143, d169604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21143, d169604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21144 q = 1) (hb : d169395 q = 1) : d169605 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21144, d169605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21144, d169605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21155 q = 1) (hb : d169395 q = 1) : d169616 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21155, d169616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21155, d169616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49166 (p : Pattern) (ha : d21161 p = 1) (hb : d169395 p = 1) : d169622 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21146 q = 1) (hb : d169395 q = 1) : d169607 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21146, d169607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49161 q ha hb
    | true =>
      simp only [d21146, d169607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49162 q ha hb
  have h2 (q : Pattern) (ha : d21147 q = 1) (hb : d169395 q = 1) : d169608 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21147, d169608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21147, d169608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21148 q = 1) (hb : d169395 q = 1) : d169609 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21148, d169609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21148, d169609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21149 q = 1) (hb : d169395 q = 1) : d169610 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21149, d169610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21149, d169610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21150 q = 1) (hb : d169395 q = 1) : d169611 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21150, d169611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21150, d169611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21156 q = 1) (hb : d169395 q = 1) : d169617 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21156, d169617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49164 q ha hb
    | true =>
      simp only [d21156, d169617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49165 q ha hb
  have h7 (q : Pattern) (ha : d21157 q = 1) (hb : d169395 q = 1) : d169618 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21157, d169618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21157, d169618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21158 q = 1) (hb : d169395 q = 1) : d169619 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21158, d169619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21158, d169619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21159 q = 1) (hb : d169395 q = 1) : d169620 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21159, d169620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21159, d169620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21160 q = 1) (hb : d169395 q = 1) : d169621 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21160, d169621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21160, d169621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21161 q = 1) (hb : d169395 q = 1) : d169622 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21161, d169622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21161, d169622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49167 (p : Pattern) (ha : d21288 p = 1) (hb : d169395 p = 1) : d169701 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21146 q = 1) (hb : d169395 q = 1) : d169607 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21146, d169607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49161 q ha hb
    | true =>
      simp only [d21146, d169607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49162 q ha hb
  have h2 (q : Pattern) (ha : d21147 q = 1) (hb : d169395 q = 1) : d169608 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21147, d169608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21147, d169608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21148 q = 1) (hb : d169395 q = 1) : d169609 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21148, d169609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21148, d169609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21149 q = 1) (hb : d169395 q = 1) : d169610 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21149, d169610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21149, d169610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21150 q = 1) (hb : d169395 q = 1) : d169611 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21150, d169611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21150, d169611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21283 q = 1) (hb : d169395 q = 1) : d169696 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21283, d169696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49162 q ha hb
    | true =>
      simp only [d21283, d169696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21284 q = 1) (hb : d169395 q = 1) : d169697 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21284, d169697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21284, d169697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21285 q = 1) (hb : d169395 q = 1) : d169698 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21285, d169698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21285, d169698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21286 q = 1) (hb : d169395 q = 1) : d169699 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21286, d169699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21286, d169699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21287 q = 1) (hb : d169395 q = 1) : d169700 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21287, d169700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21287, d169700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21288 q = 1) (hb : d169395 q = 1) : d169701 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21288, d169701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21288, d169701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49168 (p : Pattern) (ha : d21294 p = 1) (hb : d169395 p = 1) : d169707 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21283 q = 1) (hb : d169395 q = 1) : d169696 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21283, d169696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49162 q ha hb
    | true =>
      simp only [d21283, d169696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21284 q = 1) (hb : d169395 q = 1) : d169697 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21284, d169697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21284, d169697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21285 q = 1) (hb : d169395 q = 1) : d169698 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21285, d169698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21285, d169698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21286 q = 1) (hb : d169395 q = 1) : d169699 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21286, d169699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21286, d169699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21287 q = 1) (hb : d169395 q = 1) : d169700 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21287, d169700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21287, d169700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21289 q = 1) (hb : d169395 q = 1) : d169702 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21289, d169702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49165 q ha hb
    | true =>
      simp only [d21289, d169702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21290 q = 1) (hb : d169395 q = 1) : d169703 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21290, d169703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21290, d169703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21291 q = 1) (hb : d169395 q = 1) : d169704 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21291, d169704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21291, d169704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21292 q = 1) (hb : d169395 q = 1) : d169705 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21292, d169705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21292, d169705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21293 q = 1) (hb : d169395 q = 1) : d169706 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21293, d169706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21293, d169706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21294 q = 1) (hb : d169395 q = 1) : d169707 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21294, d169707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21294, d169707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49169 (p : Pattern) (ha : d21303 p = 1) (hb : d169395 p = 1) : d169716 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21289 q = 1) (hb : d169395 q = 1) : d169702 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21289, d169702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49165 q ha hb
    | true =>
      simp only [d21289, d169702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21290 q = 1) (hb : d169395 q = 1) : d169703 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21290, d169703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21290, d169703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21291 q = 1) (hb : d169395 q = 1) : d169704 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21291, d169704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21291, d169704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21292 q = 1) (hb : d169395 q = 1) : d169705 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21292, d169705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21292, d169705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21293 q = 1) (hb : d169395 q = 1) : d169706 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21293, d169706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21293, d169706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21303 q = 1) (hb : d169395 q = 1) : d169716 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21303, d169716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21303, d169716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49170 (p : Pattern) (ha : d21342 p = 1) (hb : d169395 p = 1) : d169747 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d169395 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20933 q = 1) (hb : d169395 q = 1) : d169437 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20933, d169437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49131 q ha hb
    | true =>
      simp only [d20933, d169437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d20934 q = 1) (hb : d169395 q = 1) : d169438 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20934, d169438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20934, d169438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20935 q = 1) (hb : d169395 q = 1) : d169439 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20935, d169439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20935, d169439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21332 q = 1) (hb : d169395 q = 1) : d169737 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21332, d169737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21332, d169737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21341 q = 1) (hb : d169395 q = 1) : d169746 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21341, d169746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21341, d169746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21342 q = 1) (hb : d169395 q = 1) : d169747 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21342, d169747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21342, d169747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro49171 (p : Pattern) (ha : d21398 p = 1) (hb : d169395 p = 1) : d169770 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21343 q = 1) (hb : d169395 q = 1) : d169748 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21343, d169748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49170 q ha hb
    | true =>
      simp only [d21343, d169748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21344 q = 1) (hb : d169395 q = 1) : d169749 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21344, d169749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21344, d169749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21395 q = 1) (hb : d169395 q = 1) : d169767 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21395, d169767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21395, d169767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21396 q = 1) (hb : d169395 q = 1) : d169768 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21396, d169768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21396, d169768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21397 q = 1) (hb : d169395 q = 1) : d169769 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21397, d169769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21397, d169769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21398 q = 1) (hb : d169395 q = 1) : d169770 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21398, d169770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21398, d169770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49172 (p : Pattern) (ha : d21404 p = 1) (hb : d169395 p = 1) : d169776 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21399 q = 1) (hb : d169395 q = 1) : d169771 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21399, d169771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49171 q ha hb
    | true =>
      simp only [d21399, d169771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21400 q = 1) (hb : d169395 q = 1) : d169772 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21400, d169772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21400, d169772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21401 q = 1) (hb : d169395 q = 1) : d169773 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21401, d169773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21401, d169773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21402 q = 1) (hb : d169395 q = 1) : d169774 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21402, d169774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21402, d169774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21403 q = 1) (hb : d169395 q = 1) : d169775 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21403, d169775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21403, d169775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21404 q = 1) (hb : d169395 q = 1) : d169776 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21404, d169776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21404, d169776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49173 (p : Pattern) (ha : d21166 p = 1) (hb : d169395 p = 1) : d169627 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d169395 q = 1) : d169593 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49159 q ha hb
    | true =>
      simp only [d21132, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d169395 q = 1) : d169594 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21136 q = 1) (hb : d169395 q = 1) : d169597 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49160 q ha hb
    | true =>
      simp only [d21136, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21137 q = 1) (hb : d169395 q = 1) : d169598 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21138 q = 1) (hb : d169395 q = 1) : d169599 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21138, d169599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21138, d169599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21139 q = 1) (hb : d169395 q = 1) : d169600 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21139, d169600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21139, d169600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21165 q = 1) (hb : d169395 q = 1) : d169626 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21165, d169626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21165, d169626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21166 q = 1) (hb : d169395 q = 1) : d169627 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21166, d169627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21166, d169627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49174 (p : Pattern) (ha : d21168 p = 1) (hb : d169395 p = 1) : d169629 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21136 q = 1) (hb : d169395 q = 1) : d169597 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49160 q ha hb
    | true =>
      simp only [d21136, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21137 q = 1) (hb : d169395 q = 1) : d169598 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21142 q = 1) (hb : d169395 q = 1) : d169603 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21142, d169603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21142, d169603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21143 q = 1) (hb : d169395 q = 1) : d169604 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21143, d169604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21143, d169604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21167 q = 1) (hb : d169395 q = 1) : d169628 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21167, d169628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21167, d169628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21168 q = 1) (hb : d169395 q = 1) : d169629 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21168, d169629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21168, d169629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49175 (p : Pattern) (ha : d21175 p = 1) (hb : d169395 p = 1) : d169636 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d169395 q = 1) : d169593 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49159 q ha hb
    | true =>
      simp only [d21132, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d169395 q = 1) : d169594 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21136 q = 1) (hb : d169395 q = 1) : d169597 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49160 q ha hb
    | true =>
      simp only [d21136, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21137 q = 1) (hb : d169395 q = 1) : d169598 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21138 q = 1) (hb : d169395 q = 1) : d169599 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21138, d169599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21138, d169599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21173 q = 1) (hb : d169395 q = 1) : d169634 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21173, d169634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21173, d169634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21174 q = 1) (hb : d169395 q = 1) : d169635 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21174, d169635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21174, d169635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21175 q = 1) (hb : d169395 q = 1) : d169636 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21175, d169636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21175, d169636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49176 (p : Pattern) (ha : d21178 p = 1) (hb : d169395 p = 1) : d169639 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21136 q = 1) (hb : d169395 q = 1) : d169597 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49160 q ha hb
    | true =>
      simp only [d21136, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21137 q = 1) (hb : d169395 q = 1) : d169598 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21142 q = 1) (hb : d169395 q = 1) : d169603 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21142, d169603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21142, d169603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21176 q = 1) (hb : d169395 q = 1) : d169637 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21176, d169637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21176, d169637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21177 q = 1) (hb : d169395 q = 1) : d169638 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21177, d169638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21177, d169638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21178 q = 1) (hb : d169395 q = 1) : d169639 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21178, d169639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21178, d169639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49177 (p : Pattern) (ha : d21194 p = 1) (hb : d169395 p = 1) : d169645 p = 1 := by
  have h0 (q : Pattern) (ha : d21186 q = 1) (hb : d116750 q = 1) : d21186 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20993 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21187 q = 1) (hb : d169395 q = 1) : d169643 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21187, d169395, d169643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21187, d169395, d169643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d21192 q = 1) (hb : d116750 q = 1) : d21192 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5454 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21193 q = 1) (hb : d169395 q = 1) : d169644 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21193, d169395, d169644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21193, d169395, d169644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d21194 q = 1) (hb : d169395 q = 1) : d169645 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21194, d169645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21194, d169645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49178 (p : Pattern) (ha : d21198 p = 1) (hb : d169395 p = 1) : d169649 p = 1 := by
  have h0 (q : Pattern) (ha : d5454 q = 1) (hb : d116750 q = 1) : d5454 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d28 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20995 q = 1) (hb : d169395 q = 1) : d5455 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d20995, d169395, d5455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20995, d169395, d5455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d29 q = 1) (hb : d169395 q = 1) : d29 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d21198 q = 1) (hb : d169395 q = 1) : d169649 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21198, d169649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21198, d169649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro49179 (p : Pattern) (ha : d21204 p = 1) (hb : d169395 p = 1) : d169655 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21195 q = 1) (hb : d169395 q = 1) : d169646 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21195, d169646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49177 q ha hb
    | true =>
      simp only [d21195, d169646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49141 q ha hb
  have h2 (q : Pattern) (ha : d21196 q = 1) (hb : d169395 q = 1) : d169647 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21196, d169647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21196, d169647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21197 q = 1) (hb : d169395 q = 1) : d169648 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21197, d169648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21197, d169648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21199 q = 1) (hb : d169395 q = 1) : d169650 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21199, d169650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49141 q ha hb
    | true =>
      simp only [d21199, d169650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49178 q ha hb
  have h5 (q : Pattern) (ha : d21200 q = 1) (hb : d169395 q = 1) : d169651 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21200, d169651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21200, d169651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21201 q = 1) (hb : d169395 q = 1) : d169652 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21201, d169652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21201, d169652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21202 q = 1) (hb : d169395 q = 1) : d169653 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21202, d169653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21202, d169653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d20997 q = 1) (hb : d169395 q = 1) : d169495 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20997, d169495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49141 q ha hb
    | true =>
      simp only [d20997, d169495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49124 q ha hb
  have h9 (q : Pattern) (ha : d20998 q = 1) (hb : d169395 q = 1) : d169496 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20998, d169496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20998, d169496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d20999 q = 1) (hb : d169395 q = 1) : d169497 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20999, d169497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20999, d169497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30 q = 1) (hb : d169395 q = 1) : d30 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d20894 q = 1) (hb : d169395 q = 1) : d169399 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20894, d169399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49124 q ha hb
    | true =>
      simp only [d20894, d169399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d20895 q = 1) (hb : d169395 q = 1) : d169400 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20895, d169400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20895, d169400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d20896 q = 1) (hb : d169395 q = 1) : d169401 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20896, d169401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20896, d169401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d21000 q = 1) (hb : d169395 q = 1) : d169498 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21000, d169498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21000, d169498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d21203 q = 1) (hb : d169395 q = 1) : d169654 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21203, d169654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21203, d169654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21204 q = 1) (hb : d169395 q = 1) : d169655 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21204, d169655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d21204, d169655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro49180 (p : Pattern) (ha : d21210 p = 1) (hb : d169395 p = 1) : d169661 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21205 q = 1) (hb : d169395 q = 1) : d169656 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21205, d169656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49179 q ha hb
    | true =>
      simp only [d21205, d169656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21206 q = 1) (hb : d169395 q = 1) : d169657 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21206, d169657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21206, d169657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21132 q = 1) (hb : d169395 q = 1) : d169593 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49159 q ha hb
    | true =>
      simp only [d21132, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21133 q = 1) (hb : d169395 q = 1) : d169594 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21207 q = 1) (hb : d169395 q = 1) : d169658 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21207, d169658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21207, d169658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21208 q = 1) (hb : d169395 q = 1) : d169659 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21208, d169659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21208, d169659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21209 q = 1) (hb : d169395 q = 1) : d169660 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21209, d169660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21209, d169660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21210 q = 1) (hb : d169395 q = 1) : d169661 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21210, d169661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21210, d169661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49181 (p : Pattern) (ha : d21251 p = 1) (hb : d169395 p = 1) : d169667 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d169395 q = 1) : d169593 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49159 q ha hb
    | true =>
      simp only [d21132, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d169395 q = 1) : d169594 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21248 q = 1) (hb : d169395 q = 1) : d169664 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21248, d169664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21248, d169664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21249 q = 1) (hb : d169395 q = 1) : d169665 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21249, d169665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21249, d169665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21250 q = 1) (hb : d169395 q = 1) : d169666 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21250, d169666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21250, d169666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21251 q = 1) (hb : d169395 q = 1) : d169667 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21251, d169667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21251, d169667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49182 (p : Pattern) (ha : d150078 p = 1) (hb : d169395 p = 1) : d169673 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21169 q = 1) (hb : d169395 q = 1) : d169630 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21169, d169630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49173 q ha hb
    | true =>
      simp only [d21169, d169630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49174 q ha hb
  have h2 (q : Pattern) (ha : d21170 q = 1) (hb : d169395 q = 1) : d169631 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21170, d169631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21170, d169631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21171 q = 1) (hb : d169395 q = 1) : d169632 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21171, d169632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21171, d169632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21172 q = 1) (hb : d169395 q = 1) : d169633 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21172, d169633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21172, d169633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21179 q = 1) (hb : d169395 q = 1) : d169640 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21179, d169640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49175 q ha hb
    | true =>
      simp only [d21179, d169640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49176 q ha hb
  have h6 (q : Pattern) (ha : d21180 q = 1) (hb : d169395 q = 1) : d169641 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21180, d169641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21180, d169641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21181 q = 1) (hb : d169395 q = 1) : d169642 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21181, d169642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21181, d169642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21211 q = 1) (hb : d169395 q = 1) : d169662 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21211, d169662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49180 q ha hb
    | true =>
      simp only [d21211, d169662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49161 q ha hb
  have h9 (q : Pattern) (ha : d150074 q = 1) (hb : d169395 q = 1) : d169663 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150074, d169663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150074, d169663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21252 q = 1) (hb : d169395 q = 1) : d169668 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21252, d169668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49181 q ha hb
    | true =>
      simp only [d21252, d169668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21253 q = 1) (hb : d169395 q = 1) : d169669 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21253, d169669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21253, d169669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150075 q = 1) (hb : d169395 q = 1) : d169670 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150075, d169670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150075, d169670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150076 q = 1) (hb : d169395 q = 1) : d169671 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150076, d169671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150076, d169671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150077 q = 1) (hb : d169395 q = 1) : d169672 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150077, d169672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150077, d169672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d150078 q = 1) (hb : d169395 q = 1) : d169673 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150078, d169673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150078, d169673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro49183 (p : Pattern) (ha : d21258 p = 1) (hb : d169395 p = 1) : d169674 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d169395 q = 1) : d169593 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49159 q ha hb
    | true =>
      simp only [d21132, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d169395 q = 1) : d169594 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21136 q = 1) (hb : d169395 q = 1) : d169597 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49160 q ha hb
    | true =>
      simp only [d21136, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21137 q = 1) (hb : d169395 q = 1) : d169598 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21138 q = 1) (hb : d169395 q = 1) : d169599 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21138, d169599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21138, d169599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21139 q = 1) (hb : d169395 q = 1) : d169600 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21139, d169600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21139, d169600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21165 q = 1) (hb : d169395 q = 1) : d169626 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21165, d169626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21165, d169626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21258 q = 1) (hb : d169395 q = 1) : d169674 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21258, d169674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21258, d169674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49184 (p : Pattern) (ha : d21259 p = 1) (hb : d169395 p = 1) : d169675 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21136 q = 1) (hb : d169395 q = 1) : d169597 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49160 q ha hb
    | true =>
      simp only [d21136, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21137 q = 1) (hb : d169395 q = 1) : d169598 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21142 q = 1) (hb : d169395 q = 1) : d169603 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21142, d169603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21142, d169603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21143 q = 1) (hb : d169395 q = 1) : d169604 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21143, d169604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21143, d169604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21167 q = 1) (hb : d169395 q = 1) : d169628 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21167, d169628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21167, d169628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21259 q = 1) (hb : d169395 q = 1) : d169675 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21259, d169675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21259, d169675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49185 (p : Pattern) (ha : d21264 p = 1) (hb : d169395 p = 1) : d169680 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d169395 q = 1) : d169593 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49159 q ha hb
    | true =>
      simp only [d21132, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d169395 q = 1) : d169594 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21136 q = 1) (hb : d169395 q = 1) : d169597 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49160 q ha hb
    | true =>
      simp only [d21136, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21137 q = 1) (hb : d169395 q = 1) : d169598 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21138 q = 1) (hb : d169395 q = 1) : d169599 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21138, d169599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21138, d169599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21173 q = 1) (hb : d169395 q = 1) : d169634 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21173, d169634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21173, d169634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21174 q = 1) (hb : d169395 q = 1) : d169635 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21174, d169635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21174, d169635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21264 q = 1) (hb : d169395 q = 1) : d169680 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21264, d169680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21264, d169680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49186 (p : Pattern) (ha : d21265 p = 1) (hb : d169395 p = 1) : d169681 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21136 q = 1) (hb : d169395 q = 1) : d169597 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21136, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49160 q ha hb
    | true =>
      simp only [d21136, d169597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21137 q = 1) (hb : d169395 q = 1) : d169598 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21137, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21137, d169598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21142 q = 1) (hb : d169395 q = 1) : d169603 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21142, d169603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21142, d169603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21176 q = 1) (hb : d169395 q = 1) : d169637 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21176, d169637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21176, d169637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21177 q = 1) (hb : d169395 q = 1) : d169638 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21177, d169638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21177, d169638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21265 q = 1) (hb : d169395 q = 1) : d169681 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21265, d169681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21265, d169681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49187 (p : Pattern) (ha : d21269 p = 1) (hb : d169395 p = 1) : d169685 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21205 q = 1) (hb : d169395 q = 1) : d169656 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21205, d169656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49179 q ha hb
    | true =>
      simp only [d21205, d169656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21206 q = 1) (hb : d169395 q = 1) : d169657 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21206, d169657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21206, d169657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21132 q = 1) (hb : d169395 q = 1) : d169593 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49159 q ha hb
    | true =>
      simp only [d21132, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21133 q = 1) (hb : d169395 q = 1) : d169594 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21207 q = 1) (hb : d169395 q = 1) : d169658 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21207, d169658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21207, d169658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21208 q = 1) (hb : d169395 q = 1) : d169659 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21208, d169659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21208, d169659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21209 q = 1) (hb : d169395 q = 1) : d169660 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21209, d169660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21209, d169660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21269 q = 1) (hb : d169395 q = 1) : d169685 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21269, d169685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21269, d169685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49188 (p : Pattern) (ha : d21275 p = 1) (hb : d169395 p = 1) : d169688 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21132 q = 1) (hb : d169395 q = 1) : d169593 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21132, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49159 q ha hb
    | true =>
      simp only [d21132, d169593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21133 q = 1) (hb : d169395 q = 1) : d169594 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21133, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21133, d169594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21248 q = 1) (hb : d169395 q = 1) : d169664 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21248, d169664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21248, d169664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21249 q = 1) (hb : d169395 q = 1) : d169665 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21249, d169665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21249, d169665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21250 q = 1) (hb : d169395 q = 1) : d169666 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21250, d169666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21250, d169666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21275 q = 1) (hb : d169395 q = 1) : d169688 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21275, d169688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21275, d169688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49189 (p : Pattern) (ha : d150083 p = 1) (hb : d169395 p = 1) : d169694 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21169 q = 1) (hb : d169395 q = 1) : d169630 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21169, d169630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49173 q ha hb
    | true =>
      simp only [d21169, d169630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49174 q ha hb
  have h2 (q : Pattern) (ha : d21170 q = 1) (hb : d169395 q = 1) : d169631 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21170, d169631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21170, d169631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21171 q = 1) (hb : d169395 q = 1) : d169632 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21171, d169632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21171, d169632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21172 q = 1) (hb : d169395 q = 1) : d169633 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21172, d169633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21172, d169633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21179 q = 1) (hb : d169395 q = 1) : d169640 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21179, d169640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49175 q ha hb
    | true =>
      simp only [d21179, d169640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49176 q ha hb
  have h6 (q : Pattern) (ha : d21180 q = 1) (hb : d169395 q = 1) : d169641 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21180, d169641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21180, d169641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21181 q = 1) (hb : d169395 q = 1) : d169642 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21181, d169642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21181, d169642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21211 q = 1) (hb : d169395 q = 1) : d169662 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21211, d169662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49180 q ha hb
    | true =>
      simp only [d21211, d169662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49161 q ha hb
  have h9 (q : Pattern) (ha : d150074 q = 1) (hb : d169395 q = 1) : d169663 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150074, d169663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150074, d169663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21252 q = 1) (hb : d169395 q = 1) : d169668 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21252, d169668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49181 q ha hb
    | true =>
      simp only [d21252, d169668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21253 q = 1) (hb : d169395 q = 1) : d169669 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21253, d169669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21253, d169669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150075 q = 1) (hb : d169395 q = 1) : d169670 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150075, d169670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150075, d169670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150076 q = 1) (hb : d169395 q = 1) : d169671 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150076, d169671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150076, d169671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150077 q = 1) (hb : d169395 q = 1) : d169672 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150077, d169672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150077, d169672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d21260 q = 1) (hb : d169395 q = 1) : d169676 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21260, d169676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49183 q ha hb
    | true =>
      simp only [d21260, d169676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49184 q ha hb
  have h16 (q : Pattern) (ha : d21261 q = 1) (hb : d169395 q = 1) : d169677 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21261, d169677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21261, d169677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21262 q = 1) (hb : d169395 q = 1) : d169678 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21262, d169678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d21262, d169678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d21263 q = 1) (hb : d169395 q = 1) : d169679 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21263, d169679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21263, d169679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21266 q = 1) (hb : d169395 q = 1) : d169682 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21266, d169682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49185 q ha hb
    | true =>
      simp only [d21266, d169682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49186 q ha hb
  have h20 (q : Pattern) (ha : d21267 q = 1) (hb : d169395 q = 1) : d169683 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21267, d169683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21267, d169683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d21268 q = 1) (hb : d169395 q = 1) : d169684 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21268, d169684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d21268, d169684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d21270 q = 1) (hb : d169395 q = 1) : d169686 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21270, d169686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49187 q ha hb
    | true =>
      simp only [d21270, d169686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49164 q ha hb
  have h23 (q : Pattern) (ha : d150079 q = 1) (hb : d169395 q = 1) : d169687 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150079, d169687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d150079, d169687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d21276 q = 1) (hb : d169395 q = 1) : d169689 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21276, d169689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49188 q ha hb
    | true =>
      simp only [d21276, d169689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d21277 q = 1) (hb : d169395 q = 1) : d169690 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21277, d169690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d21277, d169690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d150080 q = 1) (hb : d169395 q = 1) : d169691 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150080, d169691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d150080, d169691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d150081 q = 1) (hb : d169395 q = 1) : d169692 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150081, d169692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150081, d169692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d150082 q = 1) (hb : d169395 q = 1) : d169693 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150082, d169693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d150082, d169693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d150083 q = 1) (hb : d169395 q = 1) : d169694 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150083, d169694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150083, d169694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro49190 (p : Pattern) (ha : d150090 p = 1) (hb : d169395 p = 1) : d169714 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21270 q = 1) (hb : d169395 q = 1) : d169686 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21270, d169686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49187 q ha hb
    | true =>
      simp only [d21270, d169686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49164 q ha hb
  have h2 (q : Pattern) (ha : d150079 q = 1) (hb : d169395 q = 1) : d169687 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150079, d169687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150079, d169687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21276 q = 1) (hb : d169395 q = 1) : d169689 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21276, d169689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49188 q ha hb
    | true =>
      simp only [d21276, d169689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21277 q = 1) (hb : d169395 q = 1) : d169690 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21277, d169690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21277, d169690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150080 q = 1) (hb : d169395 q = 1) : d169691 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150080, d169691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150080, d169691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150088 q = 1) (hb : d169395 q = 1) : d169712 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150088, d169712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150088, d169712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150089 q = 1) (hb : d169395 q = 1) : d169713 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150089, d169713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150089, d169713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150090 q = 1) (hb : d169395 q = 1) : d169714 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150090, d169714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150090, d169714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49191 (p : Pattern) (ha : d21319 p = 1) (hb : d169395 p = 1) : d169724 p = 1 := by
  have h0 (q : Pattern) (ha : d21312 q = 1) (hb : d116750 q = 1) : d21312 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21074 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21313 q = 1) (hb : d169395 q = 1) : d169722 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21313, d169395, d169722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21313, d169395, d169722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d21317 q = 1) (hb : d116750 q = 1) : d21317 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d5498 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21318 q = 1) (hb : d169395 q = 1) : d169723 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21318, d169395, d169723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21318, d169395, d169723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d21319 q = 1) (hb : d169395 q = 1) : d169724 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21319, d169724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21319, d169724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49192 (p : Pattern) (ha : d21323 p = 1) (hb : d169395 p = 1) : d169728 p = 1 := by
  have h0 (q : Pattern) (ha : d5498 q = 1) (hb : d116750 q = 1) : d5498 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21076 q = 1) (hb : d169395 q = 1) : d5499 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21076, d169395, d5499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21076, d169395, d5499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d70 q = 1) (hb : d169395 q = 1) : d70 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d21323 q = 1) (hb : d169395 q = 1) : d169728 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21323, d169728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21323, d169728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro49193 (p : Pattern) (ha : d21329 p = 1) (hb : d169395 p = 1) : d169734 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21320 q = 1) (hb : d169395 q = 1) : d169725 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21320, d169725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49191 q ha hb
    | true =>
      simp only [d21320, d169725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49152 q ha hb
  have h2 (q : Pattern) (ha : d21321 q = 1) (hb : d169395 q = 1) : d169726 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21321, d169726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21321, d169726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21322 q = 1) (hb : d169395 q = 1) : d169727 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21322, d169727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21322, d169727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21324 q = 1) (hb : d169395 q = 1) : d169729 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21324, d169729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49152 q ha hb
    | true =>
      simp only [d21324, d169729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49192 q ha hb
  have h5 (q : Pattern) (ha : d21325 q = 1) (hb : d169395 q = 1) : d169730 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21325, d169730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21325, d169730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21326 q = 1) (hb : d169395 q = 1) : d169731 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21326, d169731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21326, d169731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21327 q = 1) (hb : d169395 q = 1) : d169732 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21327, d169732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21327, d169732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21078 q = 1) (hb : d169395 q = 1) : d169554 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21078, d169554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49152 q ha hb
    | true =>
      simp only [d21078, d169554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49131 q ha hb
  have h9 (q : Pattern) (ha : d21079 q = 1) (hb : d169395 q = 1) : d169555 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21079, d169555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21079, d169555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21080 q = 1) (hb : d169395 q = 1) : d169556 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21080, d169556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21080, d169556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d71 q = 1) (hb : d169395 q = 1) : d71 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d20933 q = 1) (hb : d169395 q = 1) : d169437 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20933, d169437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49131 q ha hb
    | true =>
      simp only [d20933, d169437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d20934 q = 1) (hb : d169395 q = 1) : d169438 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20934, d169438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20934, d169438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d20935 q = 1) (hb : d169395 q = 1) : d169439 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20935, d169439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20935, d169439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d21081 q = 1) (hb : d169395 q = 1) : d169557 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21081, d169557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21081, d169557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d21328 q = 1) (hb : d169395 q = 1) : d169733 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21328, d169733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21328, d169733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21329 q = 1) (hb : d169395 q = 1) : d169734 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21329, d169734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d21329, d169734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro49194 (p : Pattern) (ha : d21334 p = 1) (hb : d169395 p = 1) : d169739 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21078 q = 1) (hb : d169395 q = 1) : d169554 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21078, d169554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49152 q ha hb
    | true =>
      simp only [d21078, d169554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49131 q ha hb
  have h2 (q : Pattern) (ha : d21079 q = 1) (hb : d169395 q = 1) : d169555 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21079, d169555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21079, d169555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21080 q = 1) (hb : d169395 q = 1) : d169556 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21080, d169556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21080, d169556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d169395 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d20933 q = 1) (hb : d169395 q = 1) : d169437 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d20933, d169437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49131 q ha hb
    | true =>
      simp only [d20933, d169437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d20934 q = 1) (hb : d169395 q = 1) : d169438 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d20934, d169438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20934, d169438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20935 q = 1) (hb : d169395 q = 1) : d169439 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d20935, d169439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20935, d169439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21081 q = 1) (hb : d169395 q = 1) : d169557 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21081, d169557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21081, d169557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21332 q = 1) (hb : d169395 q = 1) : d169737 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21332, d169737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21332, d169737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21333 q = 1) (hb : d169395 q = 1) : d169738 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21333, d169738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21333, d169738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21334 q = 1) (hb : d169395 q = 1) : d169739 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21334, d169739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21334, d169739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro49195 (p : Pattern) (ha : d21340 p = 1) (hb : d169395 p = 1) : d169745 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21330 q = 1) (hb : d169395 q = 1) : d169735 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21330, d169735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49193 q ha hb
    | true =>
      simp only [d21330, d169735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21331 q = 1) (hb : d169395 q = 1) : d169736 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21331, d169736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21331, d169736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21335 q = 1) (hb : d169395 q = 1) : d169740 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21335, d169740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49194 q ha hb
    | true =>
      simp only [d21335, d169740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21336 q = 1) (hb : d169395 q = 1) : d169741 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21336, d169741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21336, d169741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21337 q = 1) (hb : d169395 q = 1) : d169742 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21337, d169742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21337, d169742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21338 q = 1) (hb : d169395 q = 1) : d169743 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21338, d169743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21338, d169743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21339 q = 1) (hb : d169395 q = 1) : d169744 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21339, d169744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21339, d169744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21340 q = 1) (hb : d169395 q = 1) : d169745 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21340, d169745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21340, d169745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49196 (p : Pattern) (ha : d21348 p = 1) (hb : d169395 p = 1) : d169753 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21335 q = 1) (hb : d169395 q = 1) : d169740 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21335, d169740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49194 q ha hb
    | true =>
      simp only [d21335, d169740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21336 q = 1) (hb : d169395 q = 1) : d169741 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21336, d169741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21336, d169741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21343 q = 1) (hb : d169395 q = 1) : d169748 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21343, d169748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49170 q ha hb
    | true =>
      simp only [d21343, d169748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21344 q = 1) (hb : d169395 q = 1) : d169749 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21344, d169749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21344, d169749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21345 q = 1) (hb : d169395 q = 1) : d169750 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21345, d169750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21345, d169750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21346 q = 1) (hb : d169395 q = 1) : d169751 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21346, d169751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21346, d169751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21347 q = 1) (hb : d169395 q = 1) : d169752 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21347, d169752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21347, d169752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21348 q = 1) (hb : d169395 q = 1) : d169753 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21348, d169753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21348, d169753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49197 (p : Pattern) (ha : d21387 p = 1) (hb : d169395 p = 1) : d169759 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21335 q = 1) (hb : d169395 q = 1) : d169740 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21335, d169740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49194 q ha hb
    | true =>
      simp only [d21335, d169740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21336 q = 1) (hb : d169395 q = 1) : d169741 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21336, d169741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21336, d169741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21384 q = 1) (hb : d169395 q = 1) : d169756 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21384, d169756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21384, d169756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21385 q = 1) (hb : d169395 q = 1) : d169757 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21385, d169757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21385, d169757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21386 q = 1) (hb : d169395 q = 1) : d169758 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21386, d169758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21386, d169758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21387 q = 1) (hb : d169395 q = 1) : d169759 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21387, d169759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21387, d169759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49198 (p : Pattern) (ha : d150100 p = 1) (hb : d169395 p = 1) : d169765 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21349 q = 1) (hb : d169395 q = 1) : d169754 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21349, d169754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49195 q ha hb
    | true =>
      simp only [d21349, d169754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49196 q ha hb
  have h2 (q : Pattern) (ha : d150096 q = 1) (hb : d169395 q = 1) : d169755 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150096, d169755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150096, d169755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21388 q = 1) (hb : d169395 q = 1) : d169760 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21388, d169760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49197 q ha hb
    | true =>
      simp only [d21388, d169760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21389 q = 1) (hb : d169395 q = 1) : d169761 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21389, d169761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21389, d169761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150097 q = 1) (hb : d169395 q = 1) : d169762 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150097, d169762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150097, d169762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150098 q = 1) (hb : d169395 q = 1) : d169763 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150098, d169763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150098, d169763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150099 q = 1) (hb : d169395 q = 1) : d169764 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150099, d169764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150099, d169764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150100 q = 1) (hb : d169395 q = 1) : d169765 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150100, d169765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150100, d169765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49199 (p : Pattern) (ha : d150106 p = 1) (hb : d169395 p = 1) : d169782 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21152 q = 1) (hb : d169395 q = 1) : d169613 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21152, d169613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21152, d169613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49163 q ha hb
  have h2 (q : Pattern) (ha : d21153 q = 1) (hb : d169395 q = 1) : d169614 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21153, d169614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21153, d169614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21162 q = 1) (hb : d169395 q = 1) : d169623 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21162, d169623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49163 q ha hb
    | true =>
      simp only [d21162, d169623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49166 q ha hb
  have h4 (q : Pattern) (ha : d21163 q = 1) (hb : d169395 q = 1) : d169624 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21163, d169624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21163, d169624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21164 q = 1) (hb : d169395 q = 1) : d169625 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d21164, d169625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21164, d169625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150084 q = 1) (hb : d169395 q = 1) : d169695 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150084, d169695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49182 q ha hb
    | true =>
      simp only [d150084, d169695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49189 q ha hb
  have h7 (q : Pattern) (ha : d21295 q = 1) (hb : d169395 q = 1) : d169708 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21295, d169708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49167 q ha hb
    | true =>
      simp only [d21295, d169708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49168 q ha hb
  have h8 (q : Pattern) (ha : d150085 q = 1) (hb : d169395 q = 1) : d169709 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150085, d169709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150085, d169709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150086 q = 1) (hb : d169395 q = 1) : d169710 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150086, d169710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150086, d169710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d150087 q = 1) (hb : d169395 q = 1) : d169711 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150087, d169711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150087, d169711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d150091 q = 1) (hb : d169395 q = 1) : d169715 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150091, d169715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150091, d169715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49190 q ha hb
  have h12 (q : Pattern) (ha : d21304 q = 1) (hb : d169395 q = 1) : d169717 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21304, d169717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21304, d169717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49169 q ha hb
  have h13 (q : Pattern) (ha : d150092 q = 1) (hb : d169395 q = 1) : d169718 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150092, d169718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150092, d169718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150093 q = 1) (hb : d169395 q = 1) : d169719 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150093, d169719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150093, d169719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d150094 q = 1) (hb : d169395 q = 1) : d169720 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150094, d169720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150094, d169720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d150095 q = 1) (hb : d169395 q = 1) : d169721 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150095, d169721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150095, d169721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d150101 q = 1) (hb : d169395 q = 1) : d169766 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150101, d169766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150101, d169766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49198 q ha hb
  have h18 (q : Pattern) (ha : d21405 q = 1) (hb : d169395 q = 1) : d169777 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21405, d169777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21405, d169777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49172 q ha hb
  have h19 (q : Pattern) (ha : d150102 q = 1) (hb : d169395 q = 1) : d169778 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150102, d169778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150102, d169778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d150103 q = 1) (hb : d169395 q = 1) : d169779 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150103, d169779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d150103, d169779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d150104 q = 1) (hb : d169395 q = 1) : d169780 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150104, d169780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d150104, d169780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d150105 q = 1) (hb : d169395 q = 1) : d169781 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150105, d169781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150105, d169781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d150106 q = 1) (hb : d169395 q = 1) : d169782 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150106, d169782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150106, d169782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro49200 (p : Pattern) (ha : d150112 p = 1) (hb : d169395 p = 1) : d169788 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150107 q = 1) (hb : d169395 q = 1) : d169783 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150107, d169783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150107, d169783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49199 q ha hb
  have h2 (q : Pattern) (ha : d150108 q = 1) (hb : d169395 q = 1) : d169784 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150108, d169784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150108, d169784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150109 q = 1) (hb : d169395 q = 1) : d169785 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150109, d169785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150109, d169785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150110 q = 1) (hb : d169395 q = 1) : d169786 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150110, d169786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150110, d169786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150111 q = 1) (hb : d169395 q = 1) : d169787 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150111, d169787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150111, d169787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150112 q = 1) (hb : d169395 q = 1) : d169788 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150112, d169788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150112, d169788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49201 (p : Pattern) (ha : d21419 p = 1) (hb : d169395 p = 1) : d169645 p = 1 := by
  have h0 (q : Pattern) (ha : d21186 q = 1) (hb : d116750 q = 1) : d21186 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20993 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21187 q = 1) (hb : d169395 q = 1) : d169643 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21187, d169395, d169643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21187, d169395, d169643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d21192 q = 1) (hb : d116750 q = 1) : d21192 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d754 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21418 q = 1) (hb : d169395 q = 1) : d169644 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21418, d169395, d169644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21418, d169395, d169644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d21419 q = 1) (hb : d169395 q = 1) : d169645 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21419, d169645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21419, d169645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49202 (p : Pattern) (ha : d21420 p = 1) (hb : d169395 p = 1) : d169790 p = 1 := by
  have h0 (q : Pattern) (ha : d20993 q = 1) (hb : d116750 q = 1) : d20993 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d754 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d20994 q = 1) (hb : d169395 q = 1) : d169493 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d20994, d169395, d169493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d20994, d169395, d169493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d757 q = 1) (hb : d169395 q = 1) : d757 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d21420 q = 1) (hb : d169395 q = 1) : d169790 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21420, d169790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21420, d169790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro49203 (p : Pattern) (ha : d21430 p = 1) (hb : d169395 p = 1) : d169800 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21421 q = 1) (hb : d169395 q = 1) : d169791 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21421, d169791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49201 q ha hb
    | true =>
      simp only [d21421, d169791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49202 q ha hb
  have h2 (q : Pattern) (ha : d21422 q = 1) (hb : d169395 q = 1) : d169792 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21422, d169792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21422, d169792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21423 q = 1) (hb : d169395 q = 1) : d169793 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21423, d169793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21423, d169793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d762 q = 1) (hb : d169395 q = 1) : d762 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21424 q = 1) (hb : d169395 q = 1) : d169794 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21424, d169794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49202 q ha hb
    | true =>
      simp only [d21424, d169794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21425 q = 1) (hb : d169395 q = 1) : d169795 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21425, d169795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21425, d169795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21426 q = 1) (hb : d169395 q = 1) : d169796 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21426, d169796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21426, d169796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21427 q = 1) (hb : d169395 q = 1) : d169797 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21427, d169797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21427, d169797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21428 q = 1) (hb : d169395 q = 1) : d169798 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21428, d169798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21428, d169798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21429 q = 1) (hb : d169395 q = 1) : d169799 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21429, d169799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21429, d169799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21430 q = 1) (hb : d169395 q = 1) : d169800 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21430, d169800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21430, d169800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro49204 (p : Pattern) (ha : d21434 p = 1) (hb : d169395 p = 1) : d169804 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d762 q = 1) (hb : d169395 q = 1) : d762 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21424 q = 1) (hb : d169395 q = 1) : d169794 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21424, d169794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49202 q ha hb
    | true =>
      simp only [d21424, d169794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21425 q = 1) (hb : d169395 q = 1) : d169795 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21425, d169795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21425, d169795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21426 q = 1) (hb : d169395 q = 1) : d169796 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21426, d169796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21426, d169796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21428 q = 1) (hb : d169395 q = 1) : d169798 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21428, d169798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21428, d169798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21433 q = 1) (hb : d169395 q = 1) : d169803 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21433, d169803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21433, d169803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21434 q = 1) (hb : d169395 q = 1) : d169804 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21434, d169804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21434, d169804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro49205 (p : Pattern) (ha : d21440 p = 1) (hb : d169395 p = 1) : d169810 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d169395 q = 1) : d169801 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49203 q ha hb
    | true =>
      simp only [d21431, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d169395 q = 1) : d169802 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21435 q = 1) (hb : d169395 q = 1) : d169805 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49204 q ha hb
    | true =>
      simp only [d21435, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21436 q = 1) (hb : d169395 q = 1) : d169806 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21437 q = 1) (hb : d169395 q = 1) : d169807 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21437, d169807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21437, d169807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21438 q = 1) (hb : d169395 q = 1) : d169808 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21438, d169808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21438, d169808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21439 q = 1) (hb : d169395 q = 1) : d169809 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21439, d169809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21439, d169809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21440 q = 1) (hb : d169395 q = 1) : d169810 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21440, d169810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21440, d169810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49206 (p : Pattern) (ha : d21444 p = 1) (hb : d169395 p = 1) : d169814 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21435 q = 1) (hb : d169395 q = 1) : d169805 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49204 q ha hb
    | true =>
      simp only [d21435, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21436 q = 1) (hb : d169395 q = 1) : d169806 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21441 q = 1) (hb : d169395 q = 1) : d169811 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21441, d169811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21441, d169811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21442 q = 1) (hb : d169395 q = 1) : d169812 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21442, d169812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21442, d169812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21443 q = 1) (hb : d169395 q = 1) : d169813 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21443, d169813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21443, d169813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21444 q = 1) (hb : d169395 q = 1) : d169814 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21444, d169814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21444, d169814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49207 (p : Pattern) (ha : d21450 p = 1) (hb : d169395 p = 1) : d169820 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21445 q = 1) (hb : d169395 q = 1) : d169815 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21445, d169815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49205 q ha hb
    | true =>
      simp only [d21445, d169815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49206 q ha hb
  have h2 (q : Pattern) (ha : d21446 q = 1) (hb : d169395 q = 1) : d169816 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21446, d169816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21446, d169816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21447 q = 1) (hb : d169395 q = 1) : d169817 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21447, d169817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21447, d169817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21448 q = 1) (hb : d169395 q = 1) : d169818 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21448, d169818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21448, d169818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21449 q = 1) (hb : d169395 q = 1) : d169819 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21449, d169819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21449, d169819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21450 q = 1) (hb : d169395 q = 1) : d169820 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21450, d169820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21450, d169820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49208 (p : Pattern) (ha : d21453 p = 1) (hb : d169395 p = 1) : d169823 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d169395 q = 1) : d169801 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49203 q ha hb
    | true =>
      simp only [d21431, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d169395 q = 1) : d169802 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21435 q = 1) (hb : d169395 q = 1) : d169805 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49204 q ha hb
    | true =>
      simp only [d21435, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21436 q = 1) (hb : d169395 q = 1) : d169806 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21437 q = 1) (hb : d169395 q = 1) : d169807 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21437, d169807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21437, d169807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21438 q = 1) (hb : d169395 q = 1) : d169808 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21438, d169808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21438, d169808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21439 q = 1) (hb : d169395 q = 1) : d169809 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21439, d169809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21439, d169809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21453 q = 1) (hb : d169395 q = 1) : d169823 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21453, d169823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21453, d169823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49209 (p : Pattern) (ha : d21454 p = 1) (hb : d169395 p = 1) : d169824 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21435 q = 1) (hb : d169395 q = 1) : d169805 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49204 q ha hb
    | true =>
      simp only [d21435, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21436 q = 1) (hb : d169395 q = 1) : d169806 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21441 q = 1) (hb : d169395 q = 1) : d169811 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21441, d169811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21441, d169811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21442 q = 1) (hb : d169395 q = 1) : d169812 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21442, d169812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21442, d169812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21443 q = 1) (hb : d169395 q = 1) : d169813 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21443, d169813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21443, d169813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21454 q = 1) (hb : d169395 q = 1) : d169824 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21454, d169824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21454, d169824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49210 (p : Pattern) (ha : d21460 p = 1) (hb : d169395 p = 1) : d169830 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21445 q = 1) (hb : d169395 q = 1) : d169815 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21445, d169815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49205 q ha hb
    | true =>
      simp only [d21445, d169815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49206 q ha hb
  have h2 (q : Pattern) (ha : d21446 q = 1) (hb : d169395 q = 1) : d169816 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21446, d169816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21446, d169816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21447 q = 1) (hb : d169395 q = 1) : d169817 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21447, d169817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21447, d169817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21448 q = 1) (hb : d169395 q = 1) : d169818 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21448, d169818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21448, d169818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21449 q = 1) (hb : d169395 q = 1) : d169819 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21449, d169819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21449, d169819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21455 q = 1) (hb : d169395 q = 1) : d169825 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21455, d169825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49208 q ha hb
    | true =>
      simp only [d21455, d169825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49209 q ha hb
  have h7 (q : Pattern) (ha : d21456 q = 1) (hb : d169395 q = 1) : d169826 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21456, d169826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21456, d169826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21457 q = 1) (hb : d169395 q = 1) : d169827 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21457, d169827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21457, d169827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21458 q = 1) (hb : d169395 q = 1) : d169828 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21458, d169828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21458, d169828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21459 q = 1) (hb : d169395 q = 1) : d169829 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21459, d169829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21459, d169829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21460 q = 1) (hb : d169395 q = 1) : d169830 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21460, d169830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21460, d169830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49211 (p : Pattern) (ha : d21591 p = 1) (hb : d169395 p = 1) : d169909 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21445 q = 1) (hb : d169395 q = 1) : d169815 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21445, d169815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49205 q ha hb
    | true =>
      simp only [d21445, d169815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49206 q ha hb
  have h2 (q : Pattern) (ha : d21446 q = 1) (hb : d169395 q = 1) : d169816 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21446, d169816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21446, d169816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21447 q = 1) (hb : d169395 q = 1) : d169817 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21447, d169817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21447, d169817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21448 q = 1) (hb : d169395 q = 1) : d169818 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21448, d169818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21448, d169818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21449 q = 1) (hb : d169395 q = 1) : d169819 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21449, d169819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21449, d169819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21586 q = 1) (hb : d169395 q = 1) : d169904 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21586, d169904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49206 q ha hb
    | true =>
      simp only [d21586, d169904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21587 q = 1) (hb : d169395 q = 1) : d169905 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21587, d169905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21587, d169905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21588 q = 1) (hb : d169395 q = 1) : d169906 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21588, d169906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21588, d169906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21589 q = 1) (hb : d169395 q = 1) : d169907 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21589, d169907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21589, d169907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21590 q = 1) (hb : d169395 q = 1) : d169908 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21590, d169908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21590, d169908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21591 q = 1) (hb : d169395 q = 1) : d169909 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21591, d169909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21591, d169909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49212 (p : Pattern) (ha : d21597 p = 1) (hb : d169395 p = 1) : d169915 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21586 q = 1) (hb : d169395 q = 1) : d169904 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21586, d169904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49206 q ha hb
    | true =>
      simp only [d21586, d169904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21587 q = 1) (hb : d169395 q = 1) : d169905 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21587, d169905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21587, d169905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21588 q = 1) (hb : d169395 q = 1) : d169906 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21588, d169906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21588, d169906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21589 q = 1) (hb : d169395 q = 1) : d169907 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21589, d169907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21589, d169907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21590 q = 1) (hb : d169395 q = 1) : d169908 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21590, d169908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21590, d169908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21592 q = 1) (hb : d169395 q = 1) : d169910 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21592, d169910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49209 q ha hb
    | true =>
      simp only [d21592, d169910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21593 q = 1) (hb : d169395 q = 1) : d169911 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21593, d169911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21593, d169911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21594 q = 1) (hb : d169395 q = 1) : d169912 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21594, d169912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21594, d169912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21595 q = 1) (hb : d169395 q = 1) : d169913 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21595, d169913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21595, d169913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21596 q = 1) (hb : d169395 q = 1) : d169914 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21596, d169914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21596, d169914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21597 q = 1) (hb : d169395 q = 1) : d169915 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21597, d169915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21597, d169915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro49213 (p : Pattern) (ha : d21606 p = 1) (hb : d169395 p = 1) : d169924 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21592 q = 1) (hb : d169395 q = 1) : d169910 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21592, d169910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49209 q ha hb
    | true =>
      simp only [d21592, d169910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21593 q = 1) (hb : d169395 q = 1) : d169911 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21593, d169911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21593, d169911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21594 q = 1) (hb : d169395 q = 1) : d169912 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21594, d169912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21594, d169912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21595 q = 1) (hb : d169395 q = 1) : d169913 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21595, d169913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21595, d169913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21596 q = 1) (hb : d169395 q = 1) : d169914 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21596, d169914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21596, d169914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21606 q = 1) (hb : d169395 q = 1) : d169924 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21606, d169924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21606, d169924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49214 (p : Pattern) (ha : d21633 p = 1) (hb : d169395 p = 1) : d169941 p = 1 := by
  have h0 (q : Pattern) (ha : d21074 q = 1) (hb : d116750 q = 1) : d21074 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d974 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21075 q = 1) (hb : d169395 q = 1) : d169552 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21075, d169395, d169552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21075, d169395, d169552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d980 q = 1) (hb : d169395 q = 1) : d980 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d21633 q = 1) (hb : d169395 q = 1) : d169941 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21633, d169941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21633, d169941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro49215 (p : Pattern) (ha : d21655 p = 1) (hb : d169395 p = 1) : d169963 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d986 q = 1) (hb : d169395 q = 1) : d986 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21637 q = 1) (hb : d169395 q = 1) : d169945 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21637, d169945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49214 q ha hb
    | true =>
      simp only [d21637, d169945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21638 q = 1) (hb : d169395 q = 1) : d169946 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21638, d169946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21638, d169946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21639 q = 1) (hb : d169395 q = 1) : d169947 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21639, d169947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21639, d169947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21645 q = 1) (hb : d169395 q = 1) : d169953 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21645, d169953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21645, d169953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21654 q = 1) (hb : d169395 q = 1) : d169962 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21654, d169962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21654, d169962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21655 q = 1) (hb : d169395 q = 1) : d169963 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21655, d169963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21655, d169963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro49216 (p : Pattern) (ha : d21715 p = 1) (hb : d169395 p = 1) : d169986 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21656 q = 1) (hb : d169395 q = 1) : d169964 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21656, d169964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49215 q ha hb
    | true =>
      simp only [d21656, d169964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21657 q = 1) (hb : d169395 q = 1) : d169965 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21657, d169965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21657, d169965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21712 q = 1) (hb : d169395 q = 1) : d169983 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21712, d169983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21712, d169983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21713 q = 1) (hb : d169395 q = 1) : d169984 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21713, d169984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21713, d169984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21714 q = 1) (hb : d169395 q = 1) : d169985 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21714, d169985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21714, d169985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21715 q = 1) (hb : d169395 q = 1) : d169986 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21715, d169986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21715, d169986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49217 (p : Pattern) (ha : d21721 p = 1) (hb : d169395 p = 1) : d169992 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21716 q = 1) (hb : d169395 q = 1) : d169987 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21716, d169987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49216 q ha hb
    | true =>
      simp only [d21716, d169987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21717 q = 1) (hb : d169395 q = 1) : d169988 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21717, d169988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21717, d169988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21718 q = 1) (hb : d169395 q = 1) : d169989 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21718, d169989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21718, d169989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21719 q = 1) (hb : d169395 q = 1) : d169990 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21719, d169990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21719, d169990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21720 q = 1) (hb : d169395 q = 1) : d169991 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d21720, d169991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21720, d169991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21721 q = 1) (hb : d169395 q = 1) : d169992 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d21721, d169992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21721, d169992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49218 (p : Pattern) (ha : d21465 p = 1) (hb : d169395 p = 1) : d169835 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d169395 q = 1) : d169801 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49203 q ha hb
    | true =>
      simp only [d21431, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d169395 q = 1) : d169802 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21435 q = 1) (hb : d169395 q = 1) : d169805 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49204 q ha hb
    | true =>
      simp only [d21435, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21436 q = 1) (hb : d169395 q = 1) : d169806 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21437 q = 1) (hb : d169395 q = 1) : d169807 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21437, d169807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21437, d169807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21438 q = 1) (hb : d169395 q = 1) : d169808 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21438, d169808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21438, d169808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21464 q = 1) (hb : d169395 q = 1) : d169834 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21464, d169834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21464, d169834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21465 q = 1) (hb : d169395 q = 1) : d169835 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21465, d169835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21465, d169835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49219 (p : Pattern) (ha : d21467 p = 1) (hb : d169395 p = 1) : d169837 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21435 q = 1) (hb : d169395 q = 1) : d169805 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49204 q ha hb
    | true =>
      simp only [d21435, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21436 q = 1) (hb : d169395 q = 1) : d169806 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21441 q = 1) (hb : d169395 q = 1) : d169811 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21441, d169811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21441, d169811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21442 q = 1) (hb : d169395 q = 1) : d169812 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21442, d169812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21442, d169812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21466 q = 1) (hb : d169395 q = 1) : d169836 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21466, d169836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21466, d169836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21467 q = 1) (hb : d169395 q = 1) : d169837 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21467, d169837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21467, d169837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49220 (p : Pattern) (ha : d21474 p = 1) (hb : d169395 p = 1) : d169844 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d169395 q = 1) : d169801 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49203 q ha hb
    | true =>
      simp only [d21431, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d169395 q = 1) : d169802 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21435 q = 1) (hb : d169395 q = 1) : d169805 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49204 q ha hb
    | true =>
      simp only [d21435, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21436 q = 1) (hb : d169395 q = 1) : d169806 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21437 q = 1) (hb : d169395 q = 1) : d169807 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21437, d169807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21437, d169807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21472 q = 1) (hb : d169395 q = 1) : d169842 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21472, d169842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21472, d169842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21473 q = 1) (hb : d169395 q = 1) : d169843 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21473, d169843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21473, d169843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21474 q = 1) (hb : d169395 q = 1) : d169844 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21474, d169844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21474, d169844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49221 (p : Pattern) (ha : d21477 p = 1) (hb : d169395 p = 1) : d169847 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21435 q = 1) (hb : d169395 q = 1) : d169805 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49204 q ha hb
    | true =>
      simp only [d21435, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21436 q = 1) (hb : d169395 q = 1) : d169806 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21441 q = 1) (hb : d169395 q = 1) : d169811 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21441, d169811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21441, d169811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21475 q = 1) (hb : d169395 q = 1) : d169845 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21475, d169845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21475, d169845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21476 q = 1) (hb : d169395 q = 1) : d169846 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21476, d169846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21476, d169846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21477 q = 1) (hb : d169395 q = 1) : d169847 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21477, d169847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21477, d169847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49222 (p : Pattern) (ha : d21493 p = 1) (hb : d169395 p = 1) : d169853 p = 1 := by
  have h0 (q : Pattern) (ha : d21485 q = 1) (hb : d116750 q = 1) : d21485 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21186 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21486 q = 1) (hb : d169395 q = 1) : d169851 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21486, d169395, d169851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21486, d169395, d169851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d21491 q = 1) (hb : d116750 q = 1) : d21491 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21192 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21492 q = 1) (hb : d169395 q = 1) : d169852 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21492, d169395, d169852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21492, d169395, d169852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d21493 q = 1) (hb : d169395 q = 1) : d169853 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21493, d169853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21493, d169853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49223 (p : Pattern) (ha : d21497 p = 1) (hb : d169395 p = 1) : d169857 p = 1 := by
  have h0 (q : Pattern) (ha : d21192 q = 1) (hb : d116750 q = 1) : d21192 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d754 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21418 q = 1) (hb : d169395 q = 1) : d169644 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21418, d169395, d169644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21418, d169395, d169644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d757 q = 1) (hb : d169395 q = 1) : d757 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d21497 q = 1) (hb : d169395 q = 1) : d169857 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21497, d169857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21497, d169857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro49224 (p : Pattern) (ha : d21503 p = 1) (hb : d169395 p = 1) : d169863 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21494 q = 1) (hb : d169395 q = 1) : d169854 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21494, d169854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49222 q ha hb
    | true =>
      simp only [d21494, d169854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49201 q ha hb
  have h2 (q : Pattern) (ha : d21495 q = 1) (hb : d169395 q = 1) : d169855 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21495, d169855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21495, d169855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21496 q = 1) (hb : d169395 q = 1) : d169856 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21496, d169856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21496, d169856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21498 q = 1) (hb : d169395 q = 1) : d169858 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21498, d169858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49201 q ha hb
    | true =>
      simp only [d21498, d169858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49223 q ha hb
  have h5 (q : Pattern) (ha : d21499 q = 1) (hb : d169395 q = 1) : d169859 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21499, d169859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21499, d169859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21500 q = 1) (hb : d169395 q = 1) : d169860 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21500, d169860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21500, d169860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21501 q = 1) (hb : d169395 q = 1) : d169861 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21501, d169861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21501, d169861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21421 q = 1) (hb : d169395 q = 1) : d169791 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21421, d169791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49201 q ha hb
    | true =>
      simp only [d21421, d169791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49202 q ha hb
  have h9 (q : Pattern) (ha : d21422 q = 1) (hb : d169395 q = 1) : d169792 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21422, d169792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21422, d169792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21423 q = 1) (hb : d169395 q = 1) : d169793 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21423, d169793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21423, d169793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d762 q = 1) (hb : d169395 q = 1) : d762 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d21424 q = 1) (hb : d169395 q = 1) : d169794 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21424, d169794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49202 q ha hb
    | true =>
      simp only [d21424, d169794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21425 q = 1) (hb : d169395 q = 1) : d169795 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21425, d169795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21425, d169795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d21426 q = 1) (hb : d169395 q = 1) : d169796 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21426, d169796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21426, d169796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d21427 q = 1) (hb : d169395 q = 1) : d169797 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21427, d169797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21427, d169797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d21502 q = 1) (hb : d169395 q = 1) : d169862 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21502, d169862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21502, d169862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21503 q = 1) (hb : d169395 q = 1) : d169863 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21503, d169863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d21503, d169863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro49225 (p : Pattern) (ha : d21509 p = 1) (hb : d169395 p = 1) : d169869 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21504 q = 1) (hb : d169395 q = 1) : d169864 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21504, d169864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49224 q ha hb
    | true =>
      simp only [d21504, d169864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21505 q = 1) (hb : d169395 q = 1) : d169865 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21505, d169865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21505, d169865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21431 q = 1) (hb : d169395 q = 1) : d169801 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49203 q ha hb
    | true =>
      simp only [d21431, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21432 q = 1) (hb : d169395 q = 1) : d169802 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21506 q = 1) (hb : d169395 q = 1) : d169866 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21506, d169866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21506, d169866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21507 q = 1) (hb : d169395 q = 1) : d169867 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21507, d169867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21507, d169867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21508 q = 1) (hb : d169395 q = 1) : d169868 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21508, d169868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21508, d169868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21509 q = 1) (hb : d169395 q = 1) : d169869 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21509, d169869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21509, d169869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49226 (p : Pattern) (ha : d21554 p = 1) (hb : d169395 p = 1) : d169875 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d169395 q = 1) : d169801 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49203 q ha hb
    | true =>
      simp only [d21431, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d169395 q = 1) : d169802 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21551 q = 1) (hb : d169395 q = 1) : d169872 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21551, d169872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21551, d169872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21552 q = 1) (hb : d169395 q = 1) : d169873 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21552, d169873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21552, d169873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21553 q = 1) (hb : d169395 q = 1) : d169874 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21553, d169874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21553, d169874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21554 q = 1) (hb : d169395 q = 1) : d169875 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21554, d169875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21554, d169875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49227 (p : Pattern) (ha : d150118 p = 1) (hb : d169395 p = 1) : d169881 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21468 q = 1) (hb : d169395 q = 1) : d169838 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21468, d169838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49218 q ha hb
    | true =>
      simp only [d21468, d169838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49219 q ha hb
  have h2 (q : Pattern) (ha : d21469 q = 1) (hb : d169395 q = 1) : d169839 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21469, d169839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21469, d169839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21470 q = 1) (hb : d169395 q = 1) : d169840 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21470, d169840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21470, d169840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21471 q = 1) (hb : d169395 q = 1) : d169841 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21471, d169841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21471, d169841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21478 q = 1) (hb : d169395 q = 1) : d169848 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21478, d169848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49220 q ha hb
    | true =>
      simp only [d21478, d169848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49221 q ha hb
  have h6 (q : Pattern) (ha : d21479 q = 1) (hb : d169395 q = 1) : d169849 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21479, d169849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21479, d169849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21480 q = 1) (hb : d169395 q = 1) : d169850 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21480, d169850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21480, d169850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21510 q = 1) (hb : d169395 q = 1) : d169870 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21510, d169870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49225 q ha hb
    | true =>
      simp only [d21510, d169870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49205 q ha hb
  have h9 (q : Pattern) (ha : d150114 q = 1) (hb : d169395 q = 1) : d169871 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150114, d169871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150114, d169871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21555 q = 1) (hb : d169395 q = 1) : d169876 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21555, d169876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49226 q ha hb
    | true =>
      simp only [d21555, d169876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21556 q = 1) (hb : d169395 q = 1) : d169877 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21556, d169877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21556, d169877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150115 q = 1) (hb : d169395 q = 1) : d169878 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150115, d169878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150115, d169878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150116 q = 1) (hb : d169395 q = 1) : d169879 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150116, d169879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150116, d169879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150117 q = 1) (hb : d169395 q = 1) : d169880 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150117, d169880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150117, d169880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d150118 q = 1) (hb : d169395 q = 1) : d169881 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150118, d169881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150118, d169881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro49228 (p : Pattern) (ha : d21561 p = 1) (hb : d169395 p = 1) : d169882 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d169395 q = 1) : d169801 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49203 q ha hb
    | true =>
      simp only [d21431, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d169395 q = 1) : d169802 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21435 q = 1) (hb : d169395 q = 1) : d169805 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49204 q ha hb
    | true =>
      simp only [d21435, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21436 q = 1) (hb : d169395 q = 1) : d169806 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21437 q = 1) (hb : d169395 q = 1) : d169807 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21437, d169807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21437, d169807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21438 q = 1) (hb : d169395 q = 1) : d169808 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21438, d169808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21438, d169808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21464 q = 1) (hb : d169395 q = 1) : d169834 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21464, d169834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21464, d169834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21561 q = 1) (hb : d169395 q = 1) : d169882 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21561, d169882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21561, d169882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49229 (p : Pattern) (ha : d21562 p = 1) (hb : d169395 p = 1) : d169883 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21435 q = 1) (hb : d169395 q = 1) : d169805 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49204 q ha hb
    | true =>
      simp only [d21435, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21436 q = 1) (hb : d169395 q = 1) : d169806 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21441 q = 1) (hb : d169395 q = 1) : d169811 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21441, d169811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21441, d169811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21442 q = 1) (hb : d169395 q = 1) : d169812 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21442, d169812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21442, d169812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21466 q = 1) (hb : d169395 q = 1) : d169836 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21466, d169836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21466, d169836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21562 q = 1) (hb : d169395 q = 1) : d169883 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21562, d169883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21562, d169883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49230 (p : Pattern) (ha : d21567 p = 1) (hb : d169395 p = 1) : d169888 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d169395 q = 1) : d169801 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49203 q ha hb
    | true =>
      simp only [d21431, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d169395 q = 1) : d169802 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21435 q = 1) (hb : d169395 q = 1) : d169805 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49204 q ha hb
    | true =>
      simp only [d21435, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21436 q = 1) (hb : d169395 q = 1) : d169806 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21437 q = 1) (hb : d169395 q = 1) : d169807 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21437, d169807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21437, d169807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21472 q = 1) (hb : d169395 q = 1) : d169842 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21472, d169842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21472, d169842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21473 q = 1) (hb : d169395 q = 1) : d169843 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21473, d169843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21473, d169843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21567 q = 1) (hb : d169395 q = 1) : d169888 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21567, d169888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21567, d169888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49231 (p : Pattern) (ha : d21568 p = 1) (hb : d169395 p = 1) : d169889 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21435 q = 1) (hb : d169395 q = 1) : d169805 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21435, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49204 q ha hb
    | true =>
      simp only [d21435, d169805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21436 q = 1) (hb : d169395 q = 1) : d169806 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21436, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21436, d169806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21441 q = 1) (hb : d169395 q = 1) : d169811 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21441, d169811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21441, d169811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21475 q = 1) (hb : d169395 q = 1) : d169845 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21475, d169845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21475, d169845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21476 q = 1) (hb : d169395 q = 1) : d169846 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21476, d169846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21476, d169846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21568 q = 1) (hb : d169395 q = 1) : d169889 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21568, d169889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21568, d169889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49232 (p : Pattern) (ha : d21572 p = 1) (hb : d169395 p = 1) : d169893 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21504 q = 1) (hb : d169395 q = 1) : d169864 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21504, d169864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49224 q ha hb
    | true =>
      simp only [d21504, d169864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21505 q = 1) (hb : d169395 q = 1) : d169865 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21505, d169865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21505, d169865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21431 q = 1) (hb : d169395 q = 1) : d169801 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49203 q ha hb
    | true =>
      simp only [d21431, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21432 q = 1) (hb : d169395 q = 1) : d169802 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21506 q = 1) (hb : d169395 q = 1) : d169866 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21506, d169866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21506, d169866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21507 q = 1) (hb : d169395 q = 1) : d169867 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21507, d169867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21507, d169867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21508 q = 1) (hb : d169395 q = 1) : d169868 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21508, d169868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21508, d169868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21572 q = 1) (hb : d169395 q = 1) : d169893 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21572, d169893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21572, d169893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49233 (p : Pattern) (ha : d21578 p = 1) (hb : d169395 p = 1) : d169896 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21431 q = 1) (hb : d169395 q = 1) : d169801 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21431, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49203 q ha hb
    | true =>
      simp only [d21431, d169801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21432 q = 1) (hb : d169395 q = 1) : d169802 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21432, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21432, d169802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21551 q = 1) (hb : d169395 q = 1) : d169872 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21551, d169872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21551, d169872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21552 q = 1) (hb : d169395 q = 1) : d169873 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21552, d169873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21552, d169873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21553 q = 1) (hb : d169395 q = 1) : d169874 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21553, d169874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21553, d169874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21578 q = 1) (hb : d169395 q = 1) : d169896 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21578, d169896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21578, d169896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49234 (p : Pattern) (ha : d150123 p = 1) (hb : d169395 p = 1) : d169902 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21468 q = 1) (hb : d169395 q = 1) : d169838 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21468, d169838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49218 q ha hb
    | true =>
      simp only [d21468, d169838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49219 q ha hb
  have h2 (q : Pattern) (ha : d21469 q = 1) (hb : d169395 q = 1) : d169839 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21469, d169839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21469, d169839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21470 q = 1) (hb : d169395 q = 1) : d169840 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21470, d169840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21470, d169840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21471 q = 1) (hb : d169395 q = 1) : d169841 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21471, d169841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21471, d169841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21478 q = 1) (hb : d169395 q = 1) : d169848 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21478, d169848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49220 q ha hb
    | true =>
      simp only [d21478, d169848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49221 q ha hb
  have h6 (q : Pattern) (ha : d21479 q = 1) (hb : d169395 q = 1) : d169849 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21479, d169849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21479, d169849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21480 q = 1) (hb : d169395 q = 1) : d169850 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21480, d169850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21480, d169850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21510 q = 1) (hb : d169395 q = 1) : d169870 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21510, d169870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49225 q ha hb
    | true =>
      simp only [d21510, d169870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49205 q ha hb
  have h9 (q : Pattern) (ha : d150114 q = 1) (hb : d169395 q = 1) : d169871 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150114, d169871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150114, d169871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21555 q = 1) (hb : d169395 q = 1) : d169876 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21555, d169876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49226 q ha hb
    | true =>
      simp only [d21555, d169876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21556 q = 1) (hb : d169395 q = 1) : d169877 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21556, d169877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21556, d169877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150115 q = 1) (hb : d169395 q = 1) : d169878 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150115, d169878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150115, d169878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150116 q = 1) (hb : d169395 q = 1) : d169879 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150116, d169879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150116, d169879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150117 q = 1) (hb : d169395 q = 1) : d169880 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150117, d169880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150117, d169880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d21563 q = 1) (hb : d169395 q = 1) : d169884 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21563, d169884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49228 q ha hb
    | true =>
      simp only [d21563, d169884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49229 q ha hb
  have h16 (q : Pattern) (ha : d21564 q = 1) (hb : d169395 q = 1) : d169885 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21564, d169885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21564, d169885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21565 q = 1) (hb : d169395 q = 1) : d169886 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21565, d169886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d21565, d169886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d21566 q = 1) (hb : d169395 q = 1) : d169887 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d21566, d169887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21566, d169887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d21569 q = 1) (hb : d169395 q = 1) : d169890 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21569, d169890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49230 q ha hb
    | true =>
      simp only [d21569, d169890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49231 q ha hb
  have h20 (q : Pattern) (ha : d21570 q = 1) (hb : d169395 q = 1) : d169891 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21570, d169891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21570, d169891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d21571 q = 1) (hb : d169395 q = 1) : d169892 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d21571, d169892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d21571, d169892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d21573 q = 1) (hb : d169395 q = 1) : d169894 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21573, d169894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49232 q ha hb
    | true =>
      simp only [d21573, d169894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49208 q ha hb
  have h23 (q : Pattern) (ha : d150119 q = 1) (hb : d169395 q = 1) : d169895 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150119, d169895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d150119, d169895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d21579 q = 1) (hb : d169395 q = 1) : d169897 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21579, d169897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49233 q ha hb
    | true =>
      simp only [d21579, d169897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d21580 q = 1) (hb : d169395 q = 1) : d169898 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21580, d169898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d21580, d169898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d150120 q = 1) (hb : d169395 q = 1) : d169899 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150120, d169899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d150120, d169899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d150121 q = 1) (hb : d169395 q = 1) : d169900 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150121, d169900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150121, d169900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d150122 q = 1) (hb : d169395 q = 1) : d169901 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150122, d169901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d150122, d169901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d150123 q = 1) (hb : d169395 q = 1) : d169902 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150123, d169902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150123, d169902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro49235 (p : Pattern) (ha : d150130 p = 1) (hb : d169395 p = 1) : d169922 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21573 q = 1) (hb : d169395 q = 1) : d169894 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21573, d169894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49232 q ha hb
    | true =>
      simp only [d21573, d169894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49208 q ha hb
  have h2 (q : Pattern) (ha : d150119 q = 1) (hb : d169395 q = 1) : d169895 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150119, d169895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150119, d169895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21579 q = 1) (hb : d169395 q = 1) : d169897 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21579, d169897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49233 q ha hb
    | true =>
      simp only [d21579, d169897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21580 q = 1) (hb : d169395 q = 1) : d169898 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21580, d169898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21580, d169898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150120 q = 1) (hb : d169395 q = 1) : d169899 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150120, d169899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150120, d169899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150128 q = 1) (hb : d169395 q = 1) : d169920 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150128, d169920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150128, d169920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150129 q = 1) (hb : d169395 q = 1) : d169921 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150129, d169921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150129, d169921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150130 q = 1) (hb : d169395 q = 1) : d169922 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150130, d169922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150130, d169922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49236 (p : Pattern) (ha : d21622 p = 1) (hb : d169395 p = 1) : d169932 p = 1 := by
  have h0 (q : Pattern) (ha : d21615 q = 1) (hb : d116750 q = 1) : d21615 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21312 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21616 q = 1) (hb : d169395 q = 1) : d169930 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21616, d169395, d169930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21616, d169395, d169930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d21620 q = 1) (hb : d116750 q = 1) : d21620 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d21317 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21621 q = 1) (hb : d169395 q = 1) : d169931 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21621, d169395, d169931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21621, d169395, d169931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d21622 q = 1) (hb : d169395 q = 1) : d169932 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21622, d169932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21622, d169932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49237 (p : Pattern) (ha : d21624 p = 1) (hb : d169395 p = 1) : d169724 p = 1 := by
  have h0 (q : Pattern) (ha : d21312 q = 1) (hb : d116750 q = 1) : d21312 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21074 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21313 q = 1) (hb : d169395 q = 1) : d169722 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21313, d169395, d169722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21313, d169395, d169722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d21317 q = 1) (hb : d116750 q = 1) : d21317 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d974 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21623 q = 1) (hb : d169395 q = 1) : d169723 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21623, d169395, d169723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21623, d169395, d169723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d21624 q = 1) (hb : d169395 q = 1) : d169724 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21624, d169724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21624, d169724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49238 (p : Pattern) (ha : d21628 p = 1) (hb : d169395 p = 1) : d169936 p = 1 := by
  have h0 (q : Pattern) (ha : d21317 q = 1) (hb : d116750 q = 1) : d21317 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d974 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21623 q = 1) (hb : d169395 q = 1) : d169723 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21623, d169395, d169723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21623, d169395, d169723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d980 q = 1) (hb : d169395 q = 1) : d980 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d21628 q = 1) (hb : d169395 q = 1) : d169936 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21628, d169936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21628, d169936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro49239 (p : Pattern) (ha : d21642 p = 1) (hb : d169395 p = 1) : d169950 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21625 q = 1) (hb : d169395 q = 1) : d169933 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21625, d169933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49236 q ha hb
    | true =>
      simp only [d21625, d169933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49237 q ha hb
  have h2 (q : Pattern) (ha : d21626 q = 1) (hb : d169395 q = 1) : d169934 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21626, d169934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21626, d169934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21627 q = 1) (hb : d169395 q = 1) : d169935 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21627, d169935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21627, d169935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21629 q = 1) (hb : d169395 q = 1) : d169937 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21629, d169937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49237 q ha hb
    | true =>
      simp only [d21629, d169937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49238 q ha hb
  have h5 (q : Pattern) (ha : d21630 q = 1) (hb : d169395 q = 1) : d169938 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21630, d169938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21630, d169938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21631 q = 1) (hb : d169395 q = 1) : d169939 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21631, d169939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21631, d169939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21632 q = 1) (hb : d169395 q = 1) : d169940 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21632, d169940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21632, d169940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21634 q = 1) (hb : d169395 q = 1) : d169942 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21634, d169942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49237 q ha hb
    | true =>
      simp only [d21634, d169942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49214 q ha hb
  have h9 (q : Pattern) (ha : d21635 q = 1) (hb : d169395 q = 1) : d169943 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21635, d169943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21635, d169943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21636 q = 1) (hb : d169395 q = 1) : d169944 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21636, d169944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21636, d169944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d986 q = 1) (hb : d169395 q = 1) : d986 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d21637 q = 1) (hb : d169395 q = 1) : d169945 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21637, d169945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49214 q ha hb
    | true =>
      simp only [d21637, d169945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21638 q = 1) (hb : d169395 q = 1) : d169946 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21638, d169946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21638, d169946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d21639 q = 1) (hb : d169395 q = 1) : d169947 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21639, d169947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21639, d169947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d21640 q = 1) (hb : d169395 q = 1) : d169948 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21640, d169948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21640, d169948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d21641 q = 1) (hb : d169395 q = 1) : d169949 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21641, d169949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21641, d169949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d21642 q = 1) (hb : d169395 q = 1) : d169950 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21642, d169950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d21642, d169950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro49240 (p : Pattern) (ha : d21647 p = 1) (hb : d169395 p = 1) : d169955 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21634 q = 1) (hb : d169395 q = 1) : d169942 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21634, d169942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49237 q ha hb
    | true =>
      simp only [d21634, d169942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49214 q ha hb
  have h2 (q : Pattern) (ha : d21635 q = 1) (hb : d169395 q = 1) : d169943 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21635, d169943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21635, d169943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21636 q = 1) (hb : d169395 q = 1) : d169944 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21636, d169944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21636, d169944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d986 q = 1) (hb : d169395 q = 1) : d986 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21637 q = 1) (hb : d169395 q = 1) : d169945 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21637, d169945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49214 q ha hb
    | true =>
      simp only [d21637, d169945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21638 q = 1) (hb : d169395 q = 1) : d169946 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21638, d169946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21638, d169946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21639 q = 1) (hb : d169395 q = 1) : d169947 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21639, d169947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21639, d169947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21640 q = 1) (hb : d169395 q = 1) : d169948 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21640, d169948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21640, d169948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21645 q = 1) (hb : d169395 q = 1) : d169953 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21645, d169953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21645, d169953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d21646 q = 1) (hb : d169395 q = 1) : d169954 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21646, d169954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21646, d169954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21647 q = 1) (hb : d169395 q = 1) : d169955 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21647, d169955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21647, d169955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro49241 (p : Pattern) (ha : d21653 p = 1) (hb : d169395 p = 1) : d169961 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21643 q = 1) (hb : d169395 q = 1) : d169951 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21643, d169951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49239 q ha hb
    | true =>
      simp only [d21643, d169951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21644 q = 1) (hb : d169395 q = 1) : d169952 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21644, d169952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21644, d169952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21648 q = 1) (hb : d169395 q = 1) : d169956 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21648, d169956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49240 q ha hb
    | true =>
      simp only [d21648, d169956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21649 q = 1) (hb : d169395 q = 1) : d169957 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21649, d169957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21649, d169957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21650 q = 1) (hb : d169395 q = 1) : d169958 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21650, d169958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21650, d169958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21651 q = 1) (hb : d169395 q = 1) : d169959 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21651, d169959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21651, d169959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21652 q = 1) (hb : d169395 q = 1) : d169960 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21652, d169960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21652, d169960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21653 q = 1) (hb : d169395 q = 1) : d169961 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21653, d169961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21653, d169961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49242 (p : Pattern) (ha : d21661 p = 1) (hb : d169395 p = 1) : d169969 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21648 q = 1) (hb : d169395 q = 1) : d169956 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21648, d169956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49240 q ha hb
    | true =>
      simp only [d21648, d169956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21649 q = 1) (hb : d169395 q = 1) : d169957 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21649, d169957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21649, d169957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21656 q = 1) (hb : d169395 q = 1) : d169964 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21656, d169964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49215 q ha hb
    | true =>
      simp only [d21656, d169964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21657 q = 1) (hb : d169395 q = 1) : d169965 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21657, d169965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21657, d169965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d21658 q = 1) (hb : d169395 q = 1) : d169966 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21658, d169966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21658, d169966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21659 q = 1) (hb : d169395 q = 1) : d169967 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21659, d169967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21659, d169967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d21660 q = 1) (hb : d169395 q = 1) : d169968 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21660, d169968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d21660, d169968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21661 q = 1) (hb : d169395 q = 1) : d169969 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21661, d169969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21661, d169969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro49243 (p : Pattern) (ha : d21704 p = 1) (hb : d169395 p = 1) : d169975 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21648 q = 1) (hb : d169395 q = 1) : d169956 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d21648, d169956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49240 q ha hb
    | true =>
      simp only [d21648, d169956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21649 q = 1) (hb : d169395 q = 1) : d169957 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d21649, d169957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21649, d169957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21701 q = 1) (hb : d169395 q = 1) : d169972 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d21701, d169972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21701, d169972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21702 q = 1) (hb : d169395 q = 1) : d169973 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d21702, d169973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21702, d169973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21703 q = 1) (hb : d169395 q = 1) : d169974 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d21703, d169974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d21703, d169974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21704 q = 1) (hb : d169395 q = 1) : d169975 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d21704, d169975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21704, d169975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro49244 (p : Pattern) (ha : d150140 p = 1) (hb : d169395 p = 1) : d169981 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21662 q = 1) (hb : d169395 q = 1) : d169970 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21662, d169970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49241 q ha hb
    | true =>
      simp only [d21662, d169970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49242 q ha hb
  have h2 (q : Pattern) (ha : d150136 q = 1) (hb : d169395 q = 1) : d169971 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150136, d169971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150136, d169971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21705 q = 1) (hb : d169395 q = 1) : d169976 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d21705, d169976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49243 q ha hb
    | true =>
      simp only [d21705, d169976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d21706 q = 1) (hb : d169395 q = 1) : d169977 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d21706, d169977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21706, d169977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150137 q = 1) (hb : d169395 q = 1) : d169978 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150137, d169978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150137, d169978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150138 q = 1) (hb : d169395 q = 1) : d169979 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150138, d169979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150138, d169979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150139 q = 1) (hb : d169395 q = 1) : d169980 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150139, d169980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150139, d169980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150140 q = 1) (hb : d169395 q = 1) : d169981 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150140, d169981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150140, d169981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro49245 (p : Pattern) (ha : d150146 p = 1) (hb : d169395 p = 1) : d169998 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21451 q = 1) (hb : d169395 q = 1) : d169821 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21451, d169821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21451, d169821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49207 q ha hb
  have h2 (q : Pattern) (ha : d21452 q = 1) (hb : d169395 q = 1) : d169822 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21452, d169822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21452, d169822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21461 q = 1) (hb : d169395 q = 1) : d169831 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21461, d169831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49207 q ha hb
    | true =>
      simp only [d21461, d169831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49210 q ha hb
  have h4 (q : Pattern) (ha : d21462 q = 1) (hb : d169395 q = 1) : d169832 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d21462, d169832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21462, d169832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d21463 q = 1) (hb : d169395 q = 1) : d169833 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d21463, d169833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21463, d169833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150124 q = 1) (hb : d169395 q = 1) : d169903 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150124, d169903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49227 q ha hb
    | true =>
      simp only [d150124, d169903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49234 q ha hb
  have h7 (q : Pattern) (ha : d21598 q = 1) (hb : d169395 q = 1) : d169916 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21598, d169916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49211 q ha hb
    | true =>
      simp only [d21598, d169916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49212 q ha hb
  have h8 (q : Pattern) (ha : d150125 q = 1) (hb : d169395 q = 1) : d169917 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150125, d169917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150125, d169917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150126 q = 1) (hb : d169395 q = 1) : d169918 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150126, d169918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150126, d169918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d150127 q = 1) (hb : d169395 q = 1) : d169919 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150127, d169919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150127, d169919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d150131 q = 1) (hb : d169395 q = 1) : d169923 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150131, d169923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150131, d169923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49235 q ha hb
  have h12 (q : Pattern) (ha : d21607 q = 1) (hb : d169395 q = 1) : d169925 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21607, d169925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21607, d169925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49213 q ha hb
  have h13 (q : Pattern) (ha : d150132 q = 1) (hb : d169395 q = 1) : d169926 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150132, d169926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150132, d169926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150133 q = 1) (hb : d169395 q = 1) : d169927 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150133, d169927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150133, d169927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d150134 q = 1) (hb : d169395 q = 1) : d169928 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150134, d169928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d150134, d169928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d150135 q = 1) (hb : d169395 q = 1) : d169929 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150135, d169929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150135, d169929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d150141 q = 1) (hb : d169395 q = 1) : d169982 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150141, d169982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150141, d169982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49244 q ha hb
  have h18 (q : Pattern) (ha : d21722 q = 1) (hb : d169395 q = 1) : d169993 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d21722, d169993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21722, d169993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49217 q ha hb
  have h19 (q : Pattern) (ha : d150142 q = 1) (hb : d169395 q = 1) : d169994 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150142, d169994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d150142, d169994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d150143 q = 1) (hb : d169395 q = 1) : d169995 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150143, d169995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d150143, d169995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d150144 q = 1) (hb : d169395 q = 1) : d169996 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150144, d169996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d150144, d169996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d150145 q = 1) (hb : d169395 q = 1) : d169997 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150145, d169997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d150145, d169997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d150146 q = 1) (hb : d169395 q = 1) : d169998 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150146, d169998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d150146, d169998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro49246 (p : Pattern) (ha : d150152 p = 1) (hb : d169395 p = 1) : d170004 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150147 q = 1) (hb : d169395 q = 1) : d169999 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150147, d169999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150147, d169999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49245 q ha hb
  have h2 (q : Pattern) (ha : d150148 q = 1) (hb : d169395 q = 1) : d170000 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150148, d170000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150148, d170000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150149 q = 1) (hb : d169395 q = 1) : d170001 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150149, d170001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150149, d170001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150150 q = 1) (hb : d169395 q = 1) : d170002 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150150, d170002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150150, d170002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150151 q = 1) (hb : d169395 q = 1) : d170003 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150151, d170003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150151, d170003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150152 q = 1) (hb : d169395 q = 1) : d170004 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150152, d170004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150152, d170004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49247 (p : Pattern) (ha : d21753 p = 1) (hb : d169395 p = 1) : d170009 p = 1 := by
  have h0 (q : Pattern) (ha : d21740 q = 1) (hb : d116750 q = 1) : d21740 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21745 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21746 q = 1) (hb : d169395 q = 1) : d170007 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21746, d169395, d170007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21746, d169395, d170007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d21751 q = 1) (hb : d116750 q = 1) : d21751 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d13028 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21752 q = 1) (hb : d169395 q = 1) : d170008 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21752, d169395, d170008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21752, d169395, d170008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d21753 q = 1) (hb : d169395 q = 1) : d170009 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21753, d170009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21753, d170009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro49248 (p : Pattern) (ha : d21761 p = 1) (hb : d169395 p = 1) : d170011 p = 1 := by
  have h0 (q : Pattern) (ha : d21745 q = 1) (hb : d116750 q = 1) : d21745 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21758 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d21759 q = 1) (hb : d169395 q = 1) : d170010 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21759, d169395, d170010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21759, d169395, d170010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d21760 q = 1) (hb : d169395 q = 1) : d21760 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d21761 q = 1) (hb : d169395 q = 1) : d170011 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d21761, d170011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21761, d170011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro49249 (p : Pattern) (ha : d21783 p = 1) (hb : d169395 p = 1) : d170024 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21762 q = 1) (hb : d169395 q = 1) : d170012 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21762, d170012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49247 q ha hb
    | true =>
      simp only [d21762, d170012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49248 q ha hb
  have h2 (q : Pattern) (ha : d21763 q = 1) (hb : d169395 q = 1) : d170013 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21763, d170013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21763, d170013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d21764 q = 1) (hb : d169395 q = 1) : d170014 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21764, d170014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21764, d170014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21771 q = 1) (hb : d169395 q = 1) : d21771 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d21772 q = 1) (hb : d169395 q = 1) : d170015 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21772, d170015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49248 q ha hb
    | true =>
      simp only [d21772, d170015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21773 q = 1) (hb : d169395 q = 1) : d170016 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21773, d170016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21773, d170016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d21774 q = 1) (hb : d169395 q = 1) : d170017 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21774, d170017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21774, d170017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d21775 q = 1) (hb : d169395 q = 1) : d170018 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21775, d170018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21775, d170018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d21777 q = 1) (hb : d169395 q = 1) : d21777 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d21778 q = 1) (hb : d169395 q = 1) : d170019 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d21778, d170019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro49248 q ha hb
    | true =>
      simp only [d21778, d170019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d21779 q = 1) (hb : d169395 q = 1) : d170020 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d21779, d170020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21779, d170020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d21780 q = 1) (hb : d169395 q = 1) : d170021 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d21780, d170021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21780, d170021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d21781 q = 1) (hb : d169395 q = 1) : d170022 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d21781, d170022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d21781, d170022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d21782 q = 1) (hb : d169395 q = 1) : d170023 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d21782, d170023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21782, d170023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d21783 q = 1) (hb : d169395 q = 1) : d170024 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d21783, d170024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d21783, d170024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h15 p ha hb
end NetHack.Soko22Hazard87
